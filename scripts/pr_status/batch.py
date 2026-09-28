"""Reconcile the status label and the Zulip post of every PR with activity since a point in time.

Usage: batch.py --since <ISO time> [--pr <number>]...

pr-status.yml runs this once per burst of PR events instead of once per event. Its concurrency
group admits one run at a time and keeps only the newest waiting one, so a burst of events costs at
most two runs; each run reconciles every PR touched since the previous successful run started,
which covers the events whose own runs were collapsed away.

A PR has had activity since T if any of these holds:

  - the PR (or its issue: comments, labels, edits) was updated at or after T;
  - a pr-build or Review run for its head was created or updated at or after T (a commit status
    does not move the PR's updated_at, so build results are found through the runs);
  - it was named with --pr (the event that started this run).

For each such PR it applies exactly the per-PR reconciliation the per-event workflows used:
labels.reconcile, then zulip.reconcile. Two things the events used to supply are derived from
current state instead:

  - a PR whose pr-build run for its head is still queued or running shows CI as running (what
    zulip-pr-status.yml painted on pr-build's `requested` event);
  - the Zulip post is created if missing only while the PR is open (`create_if_open`), which is
    what the opened/reopened events did, without letting later churn on a closed PR resurrect it.

Requires authenticated gh, TAUCETI_REVIEW_RUNNER (for labels), and ZULIP_EMAIL/ZULIP_API_KEY.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import subprocess
import sys

import core
import labels
import zulip

REPO = core.REPO
# A generous cap on one pass. More than this means a long outage; the hourly reconcile-all sweep in
# pr-labels.yml catches up whatever is left.
MAX_PRS = 150


def log(msg):
    print(msg, flush=True)


def iso(t: dt.datetime) -> str:
    return t.astimezone(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def lines(path: str, jq: str, paginate: bool = False) -> list[str]:
    return [l for l in core.gh_api(path, jq=jq, paginate=paginate).splitlines() if l]


def updated_prs(since: str) -> list[int]:
    """PRs whose updated_at is at or after `since`, newest first. The list is sorted by update time,
    so paging stops at the first page that reaches back past `since`."""
    out = []
    page = 1
    while page <= 10:
        rows = lines(f"/repos/{REPO}/pulls?state=all&sort=updated&direction=desc&per_page=100&page={page}",
                     jq='.[] | "\\(.number) \\(.updated_at)"')
        if not rows:
            break
        done = False
        for row in rows:
            number, updated = row.split()
            if updated < since:
                done = True
                break
            out.append(int(number))
        if done or len(rows) < 100:
            break
        page += 1
    return out


def open_heads() -> dict[str, int]:
    """Head sha -> PR number for every open PR."""
    heads = {}
    for row in lines(f"/repos/{REPO}/pulls?state=open&per_page=100", jq='.[] | "\\(.head.sha) \\(.number)"',
                     paginate=True):
        sha, number = row.split()
        heads[sha] = int(number)
    return heads


def workflow_runs(workflow: str, query: str) -> list[dict]:
    rows = lines(f"/repos/{REPO}/actions/workflows/{workflow}/runs?{query}&per_page=100",
                 jq='.workflow_runs[] | {head_sha, status, created_at, updated_at} | tojson')
    return [json.loads(r) for r in rows]


def touched_by_runs(since: str, heads: dict[str, int]) -> tuple[set[int], set[str]]:
    """PRs whose pr-build or Review runs moved since `since`, and the heads with a pr-build run
    still queued or in progress (whose CI therefore reads as running)."""
    prs, running = set(), set()
    for workflow in ("pr-build.yml", "review.yml"):
        for status in ("queued", "in_progress", "completed"):
            try:
                runs = workflow_runs(workflow, f"status={status}&event=pull_request_target"
                                               + (f"&created=>={since}" if status == "completed" else ""))
            except (RuntimeError, subprocess.CalledProcessError):
                continue  # Review is disabled at times; a missing workflow is not fatal
            for r in runs:
                if status == "completed" and r["updated_at"] < since:
                    continue
                if r["head_sha"] in heads:
                    prs.add(heads[r["head_sha"]])
                    if workflow == "pr-build.yml" and status != "completed":
                        running.add(r["head_sha"])
    return prs, running


def sha_of_running(heads: dict[str, int], running: set[str], number: int) -> bool:
    return any(n == number and s in running for s, n in heads.items())


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--since", required=True, help="ISO-8601 UTC time")
    ap.add_argument("--pr", type=int, action="append", default=[], help="a PR to reconcile regardless")
    ap.add_argument("--dry-run", action="store_true", help="list the PRs that would be reconciled; write nothing")
    args = ap.parse_args(argv)

    heads = open_heads()
    by_update = updated_prs(args.since)
    by_runs, running = touched_by_runs(args.since, heads)
    ordered = list(dict.fromkeys(args.pr + by_update + sorted(by_runs)))
    if len(ordered) > MAX_PRS:
        log(f"{len(ordered)} PRs touched since {args.since}; reconciling the newest {MAX_PRS}, "
            "leaving the rest to the hourly sweep")
        ordered = ordered[:MAX_PRS]
    log(f"since {args.since}: {len(ordered)} PRs to reconcile "
        f"({len(by_update)} updated, {len(by_runs)} with build or review runs, {len(args.pr)} named)")

    if args.dry_run:
        for number in ordered:
            log(f"would reconcile #{number}" + (" (CI running)" if sha_of_running(heads, running, number) else ""))
        return 0

    z = None
    email = (os.environ.get("ZULIP_EMAIL") or "").strip()
    api_key = (os.environ.get("ZULIP_API_KEY") or "").strip()
    if email and api_key:
        z = zulip.Zulip(email, api_key, (os.environ.get("ZULIP_SITE") or "https://leanprover.zulipchat.com").strip())
        bot_id = z.my_user_id()
    else:
        log("::warning::ZULIP_EMAIL / ZULIP_API_KEY not set; reconciling labels only")

    sha_of = {n: s for s, n in heads.items()}
    label_failures, zulip_failures = [], []
    for number in ordered:
        try:
            labels.reconcile(str(number))
        except core.RateLimited as exc:
            log(f"stopping: {exc}")
            return 1
        except Exception as exc:  # one PR's failure must not starve the rest
            label_failures.append(number)
            log(f"PR #{number}: label reconciliation failed: {exc}")
        if z is not None:
            ci = "running" if sha_of.get(number) in running else None
            try:
                zulip.reconcile(z, str(number), False, ci, bot_id=bot_id, create_if_open=True)
            except zulip.ConfigError as exc:
                return zulip.fail_config(str(exc))
            except Exception as exc:  # cosmetic, as in zulip.py's own reconcile
                zulip_failures.append(number)
                log(f"PR #{number}: Zulip reconciliation failed (non-fatal): {exc}")
    log(f"done: {len(ordered)} PRs; label failures {label_failures}; Zulip failures {zulip_failures}")
    return 1 if label_failures else 0


if __name__ == "__main__":
    sys.exit(main())
