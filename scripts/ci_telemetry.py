#!/usr/bin/env python3
"""Summarise one CI build's telemetry as a small JSON artifact for TauCetiCI.

    python3 scripts/ci_telemetry.py --dir pr/.lake/telemetry --out telemetry.json

Reads what `sandbox-build.sh` left in the telemetry directory:

  phases.tsv       `<phase>\t<epoch seconds>` as each phase starts, ending with `end`
  lake-build.log   the `lake build` output: one `✔ [i/N] <Verb> <Module> (<time>)` line per job

and writes `tauceti-ci.telemetry/v1`: the phases with their durations, and the build's jobs counted
by verb (Built, Unpacked from the artifact cache, Replayed, ...) with the slowest built modules.
Extra context (the runner picker's decision) comes from `--meta key=value` pairs.

Everything read here was written inside the sandbox, where candidate code runs, so it is recorded
as statistics only (`"trust": "sandbox"`) and never feeds a decision. Parsing is defensive: a
missing or garbled file yields a smaller record, not a failure.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

LINE = re.compile(r"^[✔⚠✖]\s*\[(\d+)/(\d+)\]\s+(\w+)\s+(\S+)(?:\s+\(([\d.]+)(ms|s)\))?")
MAX_MODULES = 500
MAX_LINES = 200_000


def phases(path: Path) -> list[dict]:
    marks = []
    try:
        for line in path.read_text(errors="replace").splitlines()[:1000]:
            name, _, t = line.partition("\t")
            try:
                marks.append((name.strip()[:40], float(t)))
            except ValueError:
                continue
    except OSError:
        return []
    out = []
    for (name, start), (_, end) in zip(marks, marks[1:]):
        out.append({"phase": name, "start": round(start, 3), "seconds": round(end - start, 3)})
    if marks and marks[-1][0] != "end":
        # The build stopped inside this phase (a failure): its end is unknown.
        out.append({"phase": marks[-1][0], "start": round(marks[-1][1], 3), "seconds": None})
    return out


def build_log(path: Path) -> dict:
    verbs: dict[str, int] = {}
    built: list[tuple[str, float]] = []
    total = 0
    try:
        with path.open(errors="replace") as fh:
            for i, line in enumerate(fh):
                if i >= MAX_LINES:
                    break
                m = LINE.match(line.strip())
                if not m:
                    continue
                total = max(total, int(m.group(2)))
                verb, module = m.group(3), m.group(4)
                verbs[verb] = verbs.get(verb, 0) + 1
                if verb == "Built" and m.group(5):
                    secs = float(m.group(5)) / (1000 if m.group(6) == "ms" else 1)
                    built.append((module[:200], secs))
    except OSError:
        return {}
    built.sort(key=lambda x: -x[1])
    return {
        "jobs_total": total,
        "jobs_by_verb": verbs,
        "built_seconds_total": round(sum(s for _, s in built), 1),
        "slowest_built": [{"module": m, "seconds": round(s, 2)} for m, s in built[:MAX_MODULES]],
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--meta", action="append", default=[], help="key=value context to include")
    args = ap.parse_args(argv)
    d = Path(args.dir)
    record = {
        "schema": "tauceti-ci.telemetry/v1",
        "trust": "sandbox",
        "meta": dict(kv.split("=", 1) for kv in args.meta if "=" in kv),
        "phases": phases(d / "phases.tsv"),
        "build": build_log(d / "lake-build.log"),
    }
    Path(args.out).write_text(json.dumps(record, indent=1) + "\n")


if __name__ == "__main__":
    main()
