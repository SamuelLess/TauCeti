/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.SturmTarski
public import TauCeti.Algebra.Polynomial.Sturm.PolynomialSigns

/-! # Sturm–Tarski with infinite endpoints -/

public section

namespace TauCeti.Sturm

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Sign variations at positive infinity. -/
noncomputable def variationTop (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map Polynomial.leadingCoeff)

/-- Sign variations at negative infinity. -/
noncomputable def variationBot (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree))

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Leading coefficients give the signs at positive infinity. -/
theorem variationTop_eq (cs : List (Polynomial R)) :
    variationTop cs = List.signVariations (cs.map Polynomial.leadingCoeff) := (rfl)

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Degree parity modifies the leading signs at negative infinity. -/
theorem variationBot_eq (cs : List (Polynomial R)) :
    variationBot cs =
      List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree)) := (rfl)

private theorem signs_top (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, B < x → SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  induction cs with
  | nil => exact ⟨0, by simp⟩
  | cons p cs ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨C, hC⟩ := sign_at_top p
    refine ⟨max B C, fun q hq x hx => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hC x ((le_max_right _ _).trans_lt hx)
    · exact hB q hq x ((le_max_left _ _).trans_lt hx)

private theorem signs_bot (cs : List (Polynomial R)) : ∃ B : R,
    ∀ p ∈ cs, ∀ x, x < B →
      SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  induction cs with
  | nil => exact ⟨0, by simp⟩
  | cons p cs ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨C, hC⟩ := sign_at_bot p
    refine ⟨min B C, fun q hq x hx => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hC x (hx.trans_le (min_le_right _ _))
    · exact hB q hq x (hx.trans_le (min_le_left _ _))

/-- Far enough to the right, finite evaluation realizes the infinity signs and
lies beyond every chain root. The bound belongs to the ordered field itself. -/
theorem exists_top (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, ∀ x, B < x → variation cs x = variationTop cs ∧ ∀ p ∈ cs, p.eval x ≠ 0 := by
  obtain ⟨B, hB⟩ := signs_top cs
  refine ⟨B, fun x hx => ⟨?_, ?_⟩⟩
  · rw [variation_eq, variationTop_eq]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left fun p hp => hB p hp x hx
  · intro p hp hz
    have hs := hB p hp x hx
    rw [hz, sign_zero] at hs
    exact leadingCoeff_ne_zero.mpr (hne p hp) (sign_eq_zero_iff.mp hs.symm)

/-- The analogous realization at negative infinity. -/
theorem exists_bot (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, ∀ x, x < B → variation cs x = variationBot cs ∧ ∀ p ∈ cs, p.eval x ≠ 0 := by
  obtain ⟨B, hB⟩ := signs_bot cs
  refine ⟨B, fun x hx => ⟨?_, ?_⟩⟩
  · rw [variation_eq, variationBot_eq]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left fun p hp => hB p hp x hx
  · intro p hp hz
    have hs := hB p hp x hx
    rw [hz, sign_zero] at hs
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr (hne p hp))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sign_eq_zero_iff.mp hs.symm)

/-- Sturm–Tarski on a right-unbounded interval. -/
theorem tarski_Ioi {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : TarskiSeed p f q)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0)
    {a : R} (ha : p.eval a ≠ 0) :
    (variation (p :: q :: cs) a : ℤ) - variationTop (p :: q :: cs) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB⟩ := exists_top _ h.nonzero
  let b := max a B + 1
  have hab : a < b := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hBb : B < b := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hroots : ∀ r ∈ p.roots.toFinset, r < b := by
    intro r hr
    by_contra! hbr
    exact (hB r (hBb.trans_le hbr)).2 p (by simp)
      ((mem_roots (h.nonzero p (by simp))).mp (Multiset.mem_toFinset.mp hr))
  have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (a < ·) := by
    apply Finset.filter_congr
    intro r hr
    simp [hroots r hr]
  have ht := tarski h hseed hsimple hab ha ((hB b hBb).2 p (by simp))
  rwa [(hB b hBb).1, hf] at ht

/-- Sturm–Tarski on a left-unbounded interval. -/
theorem tarski_Iio {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : TarskiSeed p f q)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0)
    {b : R} (hb : p.eval b ≠ 0) :
    (variationBot (p :: q :: cs) : ℤ) - variation (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB⟩ := exists_bot _ h.nonzero
  let a := min b B - 1
  have hab : a < b := lt_of_lt_of_le (sub_one_lt _) (min_le_left _ _)
  have haB : a < B := lt_of_lt_of_le (sub_one_lt _) (min_le_right _ _)
  have hroots : ∀ r ∈ p.roots.toFinset, a < r := by
    intro r hr
    by_contra! hra
    exact (hB r (hra.trans_lt haB)).2 p (by simp)
      ((mem_roots (h.nonzero p (by simp))).mp (Multiset.mem_toFinset.mp hr))
  have hf : p.roots.toFinset.filter (fun r => a < r ∧ r < b) = p.roots.toFinset.filter (· < b) := by
    apply Finset.filter_congr
    intro r hr
    simp [hroots r hr]
  have ht := tarski h hseed hsimple hab ((hB a haB).2 p (by simp)) hb
  rwa [(hB a haB).1, hf] at ht

/-- Sturm–Tarski on the whole real closed field. -/
theorem tarski_univ {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : TarskiSeed p f q)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (variationBot (p :: q :: cs) : ℤ) - variationTop (p :: q :: cs) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  obtain ⟨B, hB⟩ := exists_bot _ h.nonzero
  let a := B - 1
  have haB : a < B := sub_one_lt _
  have hroots : ∀ r ∈ p.roots.toFinset, a < r := by
    intro r hr
    by_contra! hra
    exact (hB r (hra.trans_lt haB)).2 p (by simp)
      ((mem_roots (h.nonzero p (by simp))).mp (Multiset.mem_toFinset.mp hr))
  have hf : p.roots.toFinset.filter (a < ·) = p.roots.toFinset := Finset.filter_true_of_mem hroots
  have ht := tarski_Ioi h hseed hsimple ((hB a haB).2 p (by simp))
  rwa [(hB a haB).1, hf] at ht


omit [IsRealClosed R] in
/-- A singleton zero-query chain on a right-unbounded interval. -/
theorem tarski_zero_Ioi {p f : Polynomial R} (hseed : TarskiSeed p f 0)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) (a : R) :
    (variation [p] a : ℤ) - variationTop [p] =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  have hz := tarski_zero hseed hsimple (p.roots.toFinset.filter (a < ·))
    (fun r hr => isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))
    (a := a) (b := a)
  simpa [variation_eq, variationTop] using hz

omit [IsRealClosed R] in
/-- A singleton zero-query chain on a left-unbounded interval. -/
theorem tarski_zero_Iio {p f : Polynomial R} (hseed : TarskiSeed p f 0)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) (b : R) :
    (variationBot [p] : ℤ) - variation [p] b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  have hz := tarski_zero hseed hsimple (p.roots.toFinset.filter (· < b))
    (fun r hr => isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))
    (a := b) (b := b)
  simpa [variation_eq, variationBot] using hz

omit [IsRealClosed R] in
/-- A singleton zero-query chain on the whole ordered field. -/
theorem tarski_zero_univ {p f : Polynomial R} (hseed : TarskiSeed p f 0)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (variationBot [p] : ℤ) - variationTop [p] =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  have hz := tarski_zero hseed hsimple p.roots.toFinset
    (fun r hr => isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))
    (a := (0 : R)) (b := 0)
  simpa [variation_eq, variationTop, variationBot] using hz

end TauCeti.Sturm
