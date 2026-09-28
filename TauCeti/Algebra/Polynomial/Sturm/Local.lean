/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Signs

/-! # Local variation jumps for regular signed polynomial chains

`Regular` records the sign conditions of a chain whose last entry has no roots.
Interior zeros preserve sign variations. Crossing a simple root of the first
entry changes the variation by the sign of its derivative times the second entry.
These local identities supply the signed root sum in `Sturm.Sum`.
-/

public section

namespace TauCeti.Sturm

open Polynomial List

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A regular signed chain has opposite neighbors at every interior zero and
no real zero in its last entry. These are the properties of a signed remainder
chain after its common polynomial factor has been removed. -/
structure Regular (cs : List (Polynomial R)) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero : ∀ q ∈ cs, q ≠ 0
  /-- The terminal polynomial has no root in the ordered field. -/
  last : ∀ q, cs.getLast? = some q → ∀ r, q.eval r ≠ 0
  /-- At an interior zero the adjacent values are nonzero and have opposite signs. -/
  alternate : ∀ (i : ℕ) (q0 q1 q2 : Polynomial R), cs[i]? = some q0 →
    cs[i + 1]? = some q1 → cs[i + 2]? = some q2 → ∀ r, q1.eval r = 0 →
    q0.eval r ≠ 0 ∧ q2.eval r ≠ 0 ∧ q0.eval r * q2.eval r < 0

namespace Regular

omit [IsStrictOrderedRing R] in
theorem tail {p : Polynomial R} {cs : List (Polynomial R)} (h : Regular (p :: cs)) :
    Regular cs where
  nonzero q hq := h.nonzero q (List.mem_cons_of_mem _ hq)
  last q hq r := by
    cases cs with
    | nil => simp at hq
    | cons q0 rest => exact h.last q (by simpa using hq) r
  alternate i q0 q1 q2 h0 h1 h2 r hz :=
    h.alternate (i + 1) q0 q1 q2
      (by simpa using h0) (by simpa using h1) (by simpa using h2) r hz

variable [IsRealClosed R]

/-- Crossing isolated interior zeros does not change variations. -/
theorem interior {cs : List (Polynomial R)} (h : Regular cs) {a r b : R}
    (har : a < r) (hrb : r < b)
    (hfront : ∀ q, cs.head? = some q → q.eval r ≠ 0)
    (hz : ∀ q ∈ cs, ∀ x ∈ Set.Icc a b, x ≠ r → q.eval x ≠ 0) :
    signVariationsAt cs a = signVariationsAt cs r ∧
      signVariationsAt cs r = signVariationsAt cs b := by
  have hab := (har.trans hrb).le
  constructor
  · refine signVariationsAt_eq cs a r
      (fun q hq => hz q hq a ⟨le_rfl, hab⟩ har.ne) hfront
      (fun q hq => h.last q hq r)
      (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) ?_
    intro q hq hqr
    exact Polynomial.sign_eval_const _ har.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  · symm
    refine signVariationsAt_eq cs b r
      (fun q hq => hz q hq b ⟨hab, le_rfl⟩ hrb.ne.symm) hfront
      (fun q hq => h.last q hq r)
      (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) ?_
    intro q hq hqr
    exact (Polynomial.sign_eval_const _ hrb.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm

/-- At a simple root of the head, the variation jump is the sign of the
product of the head derivative and the second entry. -/
theorem root_jump {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs)) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0) (hq : q.eval r ≠ 0)
    (hz : ∀ s ∈ p :: q :: cs, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAt (p :: q :: cs) b =
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  have hab := (har.trans hrb).le
  have ht := h.tail.interior har hrb
    (fun s hs => by cases hs; simpa using hq)
    (fun s hs => hz s (List.mem_cons_of_mem _ hs))
  have hpz := hz p (by simp)
  obtain ⟨hpa, hpb⟩ := Polynomial.signs_at_root p har hrb hr hd hpz
  have hqa : SignType.sign (q.eval a) = SignType.sign (q.eval r) :=
    Polynomial.sign_eval_const _ har.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hq
      · exact hz q (by simp) x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  have hqb : SignType.sign (q.eval b) = SignType.sign (q.eval r) :=
    (Polynomial.sign_eval_const _ hrb.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hq
      · exact hz q (by simp) x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm
  have ha0 := hpz a ⟨le_rfl, hab⟩ har.ne
  have hb0 := hpz b ⟨hab, le_rfl⟩ hrb.ne.symm
  have hqa0 := hz q (by simp) a ⟨le_rfl, hab⟩ har.ne
  have hqb0 := hz q (by simp) b ⟨hab, le_rfl⟩ hrb.ne.symm
  have ha : signVariationsAt (p :: q :: cs) a =
      (if -SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      signVariationsAt (q :: cs) a := by
    rw [signVariationsAt_def, List.map_cons]
    rw [signVariations_cons_of_ne_zero _ ha0, List.map_cons, firstSign_cons_of_ne_zero _ hqa0,
      hpa, hqa, neg_mul, ← sign_mul]
    simp only [signVariationsAt_def, List.map_cons]
  have hb : signVariationsAt (p :: q :: cs) b =
      (if SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      signVariationsAt (q :: cs) b := by
    rw [signVariationsAt_def, List.map_cons]
    rw [signVariations_cons_of_ne_zero _ hb0, List.map_cons, firstSign_cons_of_ne_zero _ hqb0,
      hpb, hqb, ← sign_mul]
    simp only [signVariationsAt_def, List.map_cons]
  rw [ha, hb, ht.1.trans ht.2, Nat.cast_add, Nat.cast_add]
  have numeric (s : SignType) :
      ((if -s = -1 then 1 else 0 : ℕ) : ℤ) -
        ((if s = -1 then 1 else 0 : ℕ) : ℤ) = (s : ℤ) := by
    cases s <;> decide
  have := numeric (SignType.sign (p.derivative.eval r * q.eval r))
  omega

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Consecutive entries of a regular chain cannot both vanish. -/
theorem second_eval_ne_zero {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs)) {r : R} (hr : p.eval r = 0) : q.eval r ≠ 0 := by
  cases cs with
  | nil => exact h.last q (by simp) r
  | cons s cs =>
    intro hq
    exact (h.alternate 0 p q s rfl rfl rfl r hq).1 hr


end Regular

end TauCeti.Sturm
