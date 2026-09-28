/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.SturmSigns

/-! # Local variation jumps for regular signed polynomial chains -/

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
    variation cs a = variation cs r ∧ variation cs r = variation cs b := by
  have hab := (har.trans hrb).le
  constructor
  · refine variation_at cs a r
      (fun q hq => hz q hq a ⟨le_rfl, hab⟩ har.ne) hfront
      (fun q hq => h.last q hq r)
      (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) ?_
    intro q hq hqr
    exact eval_sign_eq har.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  · symm
    refine variation_at cs b r
      (fun q hq => hz q hq b ⟨hab, le_rfl⟩ hrb.ne.symm) hfront
      (fun q hq => h.last q hq r)
      (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 r) ?_
    intro q hq hqr
    exact (eval_sign_eq hrb.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hqr
      · exact hz q hq x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm

/-- Near an isolated simple root, the head polynomial changes from the negative
of its derivative's sign to its derivative's sign. -/
theorem root_signs {p : Polynomial R} {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0)
    (hz : ∀ x ∈ Set.Icc a b, x ≠ r → p.eval x ≠ 0) :
    SignType.sign (p.eval a) = -SignType.sign (p.derivative.eval r) ∧
    SignType.sign (p.eval b) = SignType.sign (p.derivative.eval r) := by
  obtain ⟨d, hp⟩ := (dvd_iff_isRoot.mpr hr : X - C r ∣ p)
  have hdr : p.derivative.eval r = d.eval r := by
    rw [hp, derivative_mul]
    simp
  have hdz : ∀ x ∈ Set.Icc a b, d.eval x ≠ 0 := by
    intro x hx
    by_cases hxr : x = r
    · simpa [hxr, hdr] using hd
    · intro hdx
      apply hz x hx hxr
      simp [hp, hdx]
  have hda := eval_sign_eq har.le (fun x hx => hdz x ⟨hx.1, hx.2.trans hrb.le⟩)
  have hdb := eval_sign_eq hrb.le (fun x hx => hdz x ⟨har.le.trans hx.1, hx.2⟩)
  constructor
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_neg (sub_neg.mpr har), neg_one_mul, hda]
  · rw [hdr, hp, eval_mul, eval_sub, eval_X, eval_C, sign_mul,
      sign_pos (sub_pos.mpr hrb), one_mul, ← hdb]

/-- At a simple root of the head, the variation jump is the sign of the
product of the head derivative and the second entry. -/
theorem root_jump {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs)) {a r b : R} (har : a < r) (hrb : r < b)
    (hr : p.eval r = 0) (hd : p.derivative.eval r ≠ 0) (hq : q.eval r ≠ 0)
    (hz : ∀ s ∈ p :: q :: cs, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0) :
    (variation (p :: q :: cs) a : ℤ) - variation (p :: q :: cs) b =
      (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  have hab := (har.trans hrb).le
  have ht := h.tail.interior har hrb
    (fun s hs => by cases hs; simpa using hq)
    (fun s hs => hz s (List.mem_cons_of_mem _ hs))
  have hpz := hz p (by simp)
  obtain ⟨hpa, hpb⟩ := root_signs har hrb hr hd hpz
  have hqa : SignType.sign (q.eval a) = SignType.sign (q.eval r) :=
    eval_sign_eq har.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hq
      · exact hz q (by simp) x ⟨hx.1, hx.2.trans hrb.le⟩ hxr)
  have hqb : SignType.sign (q.eval b) = SignType.sign (q.eval r) :=
    (eval_sign_eq hrb.le (fun x hx => by
      by_cases hxr : x = r
      · simpa [hxr] using hq
      · exact hz q (by simp) x ⟨har.le.trans hx.1, hx.2⟩ hxr)).symm
  have ha0 := hpz a ⟨le_rfl, hab⟩ har.ne
  have hb0 := hpz b ⟨hab, le_rfl⟩ hrb.ne.symm
  have hqa0 := hz q (by simp) a ⟨le_rfl, hab⟩ har.ne
  have hqb0 := hz q (by simp) b ⟨hab, le_rfl⟩ hrb.ne.symm
  have ha : variation (p :: q :: cs) a =
      (if -SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      variation (q :: cs) a := by
    rw [variation_eq, List.map_cons]
    rw [signVariations_cons _ ha0, List.map_cons, firstSign_cons_ne _ hqa0,
      hpa, hqa, neg_mul, ← sign_mul]
    simp only [variation_eq, List.map_cons]
  have hb : variation (p :: q :: cs) b =
      (if SignType.sign (p.derivative.eval r * q.eval r) = -1 then 1 else 0) +
      variation (q :: cs) b := by
    rw [variation_eq, List.map_cons]
    rw [signVariations_cons _ hb0, List.map_cons, firstSign_cons_ne _ hqb0,
      hpb, hqb, ← sign_mul]
    simp only [variation_eq, List.map_cons]
  rw [ha, hb, ht.1.trans ht.2, Nat.cast_add, Nat.cast_add]
  have numeric (s : SignType) :
      ((if -s = -1 then 1 else 0 : ℕ) : ℤ) -
        ((if s = -1 then 1 else 0 : ℕ) : ℤ) = (s : ℤ) := by
    cases s <;> decide
  have := numeric (SignType.sign (p.derivative.eval r * q.eval r))
  omega

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Consecutive entries of a regular chain cannot both vanish. -/
theorem second_ne {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs)) {r : R} (hr : p.eval r = 0) : q.eval r ≠ 0 := by
  cases cs with
  | nil => exact h.last q (by simp) r
  | cons s cs =>
    intro hq
    exact (h.alternate 0 p q s rfl rfl rfl r hq).1 hr


end Regular

end TauCeti.Sturm
