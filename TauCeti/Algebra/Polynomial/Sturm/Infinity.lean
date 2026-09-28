/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Tarski
public import TauCeti.Algebra.Polynomial.Eval.Infinity

/-! # Sturm–Tarski with infinite endpoints

Leading coefficients and degree parity compute the sign variations at both
infinities. These give half-line and whole-field Sturm–Tarski identities for
signed remainder chains and for `Polynomial.sturmSeq`, including root counts.
-/

public section

namespace TauCeti.Sturm

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Sign variations at positive infinity. -/
noncomputable def signVariationsAtTop (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map Polynomial.leadingCoeff)

/-- Sign variations at negative infinity. -/
noncomputable def signVariationsAtBot (cs : List (Polynomial R)) : ℕ :=
  List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree))

omit [IsStrictOrderedRing R] in
/-- Unfold positive-infinity variations as variations of the leading coefficients. -/
theorem signVariationsAtTop_def (cs : List (Polynomial R)) :
    signVariationsAtTop cs = List.signVariations (cs.map Polynomial.leadingCoeff) := (rfl)

omit [IsStrictOrderedRing R] in
/-- Unfold negative-infinity variations using leading coefficients and degree parity. -/
theorem signVariationsAtBot_def (cs : List (Polynomial R)) :
    signVariationsAtBot cs =
      List.signVariations (cs.map (fun p => p.leadingCoeff * (-1) ^ p.natDegree)) := (rfl)

omit [IsStrictOrderedRing R] in
@[simp]
theorem signVariationsAtTop_nil : signVariationsAtTop ([] : List R[X]) = 0 := by
  simp [signVariationsAtTop_def]

omit [IsStrictOrderedRing R] in
@[simp]
theorem signVariationsAtTop_singleton (p : R[X]) : signVariationsAtTop [p] = 0 := by
  simp [signVariationsAtTop_def]

omit [IsStrictOrderedRing R] in
@[simp]
theorem signVariationsAtBot_nil : signVariationsAtBot ([] : List R[X]) = 0 := by
  simp [signVariationsAtBot_def]

omit [IsStrictOrderedRing R] in
@[simp]
theorem signVariationsAtBot_singleton (p : R[X]) : signVariationsAtBot [p] = 0 := by
  simp [signVariationsAtBot_def]

/-- Far enough to the right, finite evaluation realizes the infinity signs and
lies beyond every chain root. The bound belongs to the ordered field itself. -/
theorem exists_top (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, ∀ x, B < x →
      signVariationsAt cs x = signVariationsAtTop cs ∧ ∀ p ∈ cs, p.eval x ≠ 0 := by
  obtain ⟨B, hB⟩ := List.exists_signs_atTop cs
  refine ⟨B, fun x hx => ⟨?_, ?_⟩⟩
  · rw [signVariationsAt_def, signVariationsAtTop_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left fun p hp => hB p hp x hx
  · intro p hp hz
    have hs := hB p hp x hx
    rw [hz, sign_zero] at hs
    exact leadingCoeff_ne_zero.mpr (hne p hp) (sign_eq_zero_iff.mp hs.symm)

/-- The analogous realization at negative infinity. -/
theorem exists_bot (cs : List (Polynomial R)) (hne : ∀ p ∈ cs, p ≠ 0) :
    ∃ B : R, ∀ x, x < B →
      signVariationsAt cs x = signVariationsAtBot cs ∧ ∀ p ∈ cs, p.eval x ≠ 0 := by
  obtain ⟨B, hB⟩ := List.exists_signs_atBot cs
  refine ⟨B, fun x hx => ⟨?_, ?_⟩⟩
  · rw [signVariationsAt_def, signVariationsAtBot_def]
    apply List.signVariations_congr
    simp only [List.map_map]
    exact List.map_congr_left fun p hp => hB p hp x hx
  · intro p hp hz
    have hs := hB p hp x hx
    rw [hz, sign_zero] at hs
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr (hne p hp))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (sign_eq_zero_iff.mp hs.symm)

variable [IsRealClosed R]

/-- Sturm–Tarski on a right-unbounded interval. -/
theorem tarski_Ioi {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    {a : R} (hsimple : ∀ r, a < r → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (ha : p.eval a ≠ 0) :
    (signVariationsAt (p :: q :: cs) a : ℤ) - signVariationsAtTop (p :: q :: cs) =
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
  have ht := tarski h hseed (fun r har _ => hsimple r har) hab ha ((hB b hBb).2 p (by simp))
  rwa [(hB b hBb).1, hf] at ht

/-- Sturm–Tarski on a left-unbounded interval. -/
theorem tarski_Iio {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    {b : R} (hsimple : ∀ r, r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (p :: q :: cs) : ℤ) - signVariationsAt (p :: q :: cs) b =
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
  have ht := tarski h hseed (fun r _ hrb => hsimple r hrb) hab ((hB a haB).2 p (by simp)) hb
  rwa [(hB a haB).1, hf] at ht

/-- Sturm–Tarski on the whole real closed field. -/
theorem tarski_univ {p f q : Polynomial R} {cs : List (Polynomial R)}
    (h : Signed (p :: q :: cs)) (hseed : IsTarskiSeed p f q)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (signVariationsAtBot (p :: q :: cs) : ℤ) - signVariationsAtTop (p :: q :: cs) =
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
  have ht := tarski_Ioi h hseed (fun r _ => hsimple r) ((hB a haB).2 p (by simp))
  rwa [(hB a haB).1, hf] at ht


/-- Sturm–Tarski for Mathlib's signed remainder sequence on a right-unbounded interval. -/
theorem tarski_sturmSeq_Ioi (p f : R[X]) (hp : p ≠ 0)
    {a : R} (hsimple : ∀ r, a < r → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (ha : p.eval a ≠ 0) :
    (signVariationsAt (sturmSeq p (f * p.derivative)) a : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset.filter (a < ·), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hseed := IsTarskiSeed.mul_derivative p f
  by_cases hq : f * p.derivative = 0
  · rw [hq] at hseed ⊢
    rw [sturmSeq_zero_right, ite_eq_right hp]
    simpa using (hseed.sum_sign_eq_zero _
      (fun r hr => hsimple r (Finset.mem_filter.mp hr).2
        (isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)))
      (fun r hr => isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))).symm
  · have hsigned := signed_sturmSeq p (f * p.derivative)
    rw [sturmSeq_cons hp, sturmSeq_cons hq] at hsigned ⊢
    exact tarski_Ioi hsigned hseed hsimple ha

/-- Sturm–Tarski for Mathlib's signed remainder sequence on a left-unbounded interval. -/
theorem tarski_sturmSeq_Iio (p f : R[X]) (hp : p ≠ 0)
    {b : R} (hsimple : ∀ r, r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAt (sturmSeq p (f * p.derivative)) b =
      ∑ r ∈ p.roots.toFinset.filter (· < b), (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hseed := IsTarskiSeed.mul_derivative p f
  by_cases hq : f * p.derivative = 0
  · rw [hq] at hseed ⊢
    rw [sturmSeq_zero_right, ite_eq_right hp]
    simpa using (hseed.sum_sign_eq_zero _
      (fun r hr => hsimple r (Finset.mem_filter.mp hr).2
        (isRoot_of_mem_roots (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)))
      (fun r hr => isRoot_of_mem_roots
        (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1))).symm
  · have hsigned := signed_sturmSeq p (f * p.derivative)
    rw [sturmSeq_cons hp, sturmSeq_cons hq] at hsigned ⊢
    exact tarski_Iio hsigned hseed hsimple hb

/-- Sturm–Tarski for Mathlib's signed remainder sequence on the whole real closed field. -/
theorem tarski_sturmSeq_univ (p f : R[X]) (hp : p ≠ 0)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (signVariationsAtBot (sturmSeq p (f * p.derivative)) : ℤ) -
        signVariationsAtTop (sturmSeq p (f * p.derivative)) =
      ∑ r ∈ p.roots.toFinset, (SignType.sign (f.eval r) : ℤ) := by
  classical
  have hseed := IsTarskiSeed.mul_derivative p f
  by_cases hq : f * p.derivative = 0
  · rw [hq] at hseed ⊢
    rw [sturmSeq_zero_right, ite_eq_right hp]
    simpa using (hseed.sum_sign_eq_zero _
      (fun r hr => hsimple r (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr)))
      (fun r hr => isRoot_of_mem_roots (Multiset.mem_toFinset.mp hr))).symm
  · have hsigned := signed_sturmSeq p (f * p.derivative)
    rw [sturmSeq_cons hp, sturmSeq_cons hq] at hsigned ⊢
    exact tarski_univ hsigned hseed hsimple

/-- Classical Sturm counting of distinct roots in a right-unbounded interval. -/
theorem sturm_Ioi (p : R[X]) (hp : p ≠ 0) {a : R}
    (hsimple : ∀ r, a < r → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (ha : p.eval a ≠ 0) :
    (signVariationsAt (sturmSeq p p.derivative) a : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      (p.roots.toFinset.filter (a < ·)).card := by
  classical
  simpa using tarski_sturmSeq_Ioi p 1 hp hsimple ha

/-- Classical Sturm counting of distinct roots in a left-unbounded interval. -/
theorem sturm_Iio (p : R[X]) (hp : p ≠ 0) {b : R}
    (hsimple : ∀ r, r < b → p.eval r = 0 → p.derivative.eval r ≠ 0)
    (hb : p.eval b ≠ 0) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAt (sturmSeq p p.derivative) b =
      (p.roots.toFinset.filter (· < b)).card := by
  classical
  simpa using tarski_sturmSeq_Iio p 1 hp hsimple hb

/-- Classical Sturm counting of all distinct roots of a polynomial with simple roots. -/
theorem sturm_univ (p : R[X]) (hp : p ≠ 0)
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0) :
    (signVariationsAtBot (sturmSeq p p.derivative) : ℤ) -
        signVariationsAtTop (sturmSeq p p.derivative) =
      p.roots.toFinset.card := by
  simpa using tarski_sturmSeq_univ p 1 hp hsimple

end TauCeti.Sturm
