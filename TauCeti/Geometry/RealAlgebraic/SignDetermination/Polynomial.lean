/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Moments
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Sign determination from polynomial sign sums

`signCount` counts points realizing a sign condition, and `signSum` is the
integer sum of signs on a specified finite set. `signSum_eq_sum_signCount` expresses
the sign sum of a product as a moment of these counts. `fullInverse_mulVec_signSum` inverts
the full moment system over the rationals.

These statements hold over any linearly ordered commutative ring. For root sign determination,
take the finite set to be the distinct roots of a nonzero polynomial, possibly
restricted to an interval. The zero polynomial must be handled separately:
its zero set is not represented by its empty `Polynomial.roots` multiset.

## References

M. Ben-Or, D. Kozen, and J. Reif,
[The complexity of elementary algebra and geometry](https://doi.org/10.1016/0022-0000(86)90029-2),
Journal of Computer and System Sciences 32 (1986), 251–264, for BKR sign determination.
-/

public section

open Polynomial SignType
open scoped Matrix

namespace TauCeti.SignDetermination

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomial evaluation followed by sign and a sign-code cast. -/
noncomputable def signEval {K : Type*} [MulZeroOneClass K] [HasDistribNeg K] (x : R) : R[X] →*₀ K :=
  SignType.castHom.comp (signHom.comp (Polynomial.evalRingHom x).toMonoidWithZeroHom)

@[simp] theorem signEval_apply {K : Type*} [MulZeroOneClass K] [HasDistribNeg K]
    (x : R) (p : R[X]) :
    signEval x p = (sign (p.eval x) : K) := (rfl)

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, signEval x.val p

/-- Sign sums are integer sums of pointwise polynomial signs. -/
theorem signSum_eq_sum_subtype (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x : Z, (sign (p.eval x.val) : ℤ) := (rfl)

/-- Sign sums expressed directly over the original finite set. -/
theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x ∈ Z, (sign (p.eval x) : ℤ) := by
  rw [signSum_eq_sum_subtype, Finset.sum_coe_sort Z (fun x : R => (sign (p.eval x) : ℤ))]

@[simp] theorem signSum_empty (p : R[X]) : signSum ∅ p = 0 := by
  simp [signSum_eq_sum]

@[simp] theorem signSum_zero (Z : Finset R) : signSum Z 0 = 0 := by
  simp [signSum_eq_sum]

@[simp] theorem signSum_one (Z : Finset R) : signSum Z 1 = Z.card := by
  simp [signSum_eq_sum]

/-- A finite sign sum is the number of positive evaluations minus the number of negative ones. -/
theorem signSum_eq_card_sub_card (Z : Finset R) (p : R[X]) :
    signSum Z p = ((Z.filter (fun x => 0 < p.eval x)).card : ℤ) -
      (Z.filter (fun x => p.eval x < 0)).card := by
  classical
  rw [signSum_eq_sum]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hpos : 0 < p.eval x
  · have hneg : ¬ p.eval x < 0 := not_lt_of_ge hpos.le
    simp [hpos, hneg]
  · by_cases hneg : p.eval x < 0 <;> simp [sign_apply, hpos, hneg]

omit [IsStrictOrderedRing R] in
/-- The number of points realizing a specified polynomial sign condition. -/
noncomputable def signCount {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) : ℕ :=
  fiberCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ

omit [IsStrictOrderedRing R] in
/-- Polynomial sign counts are multiplicities in the finite family of pointwise signs. -/
theorem signCount_eq_fiberCount {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = fiberCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := (rfl)

omit [IsStrictOrderedRing R] in
/-- Sign counts are cardinalities of the realizing subset of the original finite set. -/
theorem signCount_eq_card_filter {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = (Z.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card := by
  classical
  simp only [signCount_eq_fiberCount, fiberCount_eq_card_filter, Finset.card_filter,
    funext_iff]
  exact Finset.sum_coe_sort Z
    (fun x : R => if ∀ j, sign ((Q j).eval x) = σ j then (1 : ℕ) else 0)

omit [IsStrictOrderedRing R] in
@[simp] theorem signCount_empty {J : Type*} [Fintype J]
    (Q : J → R[X]) (σ : J → SignType) : signCount ∅ Q σ = 0 := by
  simp [signCount_eq_card_filter]

omit [IsStrictOrderedRing R] in
/-- The sign conditions partition the original finite set of points. -/
theorem sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) : ∑ σ, signCount Z Q σ = Z.card := by
  classical
  simpa only [signCount_eq_fiberCount, Fintype.card_coe] using
    sum_fiberCount (fun x : Z => fun j => sign ((Q j).eval x.val))

omit [IsStrictOrderedRing R] in
/-- A positive sign count is equivalent to realization at a point of the finite set. -/
@[simp] theorem signCount_pos {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount Z Q σ ↔ ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp [signCount_eq_card_filter, Finset.card_pos, Finset.Nonempty]

/-- The sign sum of a product is the sum of the products of its pointwise signs. -/
private theorem signSum_prod {J : Type*} [Fintype J] (Z : Finset R) (Q : J → R[X]) :
    signSum Z (∏ j, Q j) = ∑ x : Z, ∏ j, (sign ((Q j).eval x.val) : ℤ) := by
  simp only [signSum, map_prod, signEval_apply]

/-- The sign sum of a product of powers is the sum of the pointwise sign products. -/
private theorem signSum_prod_pow {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ x : Z, ∏ j, (sign ((Q j).eval x.val) : ℤ) ^ e j := by
  simp only [signSum_prod, eval_pow, sign_pow, SignType.coe_pow]

/-- The polynomial moment identity on any complete restricted column set and
any selected exponent rows. Exponents need not be bounded by two. -/
theorem mulVec_signCount {J C I : Type*} [Fintype J]
    [Fintype C] (Z : Finset R) (Q : J → R[X])
    (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x ∈ Z, ∃ c, columns c = fun j => sign ((Q j).eval x)) :
    (Matrix.of fun i c => ∏ j, (columns c j : ℤ) ^ rows i j) *ᵥ
        (fun c => (signCount Z Q (columns c) : ℤ)) =
      fun i => signSum Z (∏ j, Q j ^ rows i j) := by
  classical
  simp_rw [signSum_prod_pow]
  simpa only [signCount_eq_fiberCount] using
    mulVec_fiberCount _ columns hinj (fun x : Z => cover x.val x.property)
      (fun i σ => ∏ j, (σ j : ℤ) ^ rows i j)

/-- All ternary moments determine the exact multiplicity of every sign pattern. -/
theorem fullInverse_mulVec_signSum {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (signSum Z (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount Z Q σ : ℚ) := by
  simp_rw [signSum_prod_pow]
  simpa only [Int.cast_sum, Int.cast_prod, Int.cast_pow,
    signCount_eq_fiberCount, SignType.intCast_cast] using
    fullInverse_mulVec J (fun x : Z => fun j => sign ((Q j).eval x.val))

/-- The integer BKR moment identity on a finite set of sample points. -/
theorem signSum_eq_sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) * (signCount Z Q σ : ℤ) := by
  classical
  simp only [signSum_prod_pow]
  simpa only [id_eq, signCount_eq_fiberCount] using
    (sum_mul_fiberCount (fun x : Z => fun j => sign ((Q j).eval x.val)) id
      Function.injective_id (fun x => ⟨_, rfl⟩)
      (fun σ => ∏ j, (σ j : ℤ) ^ e j)).symm

/-- The recovered sign pattern is positive exactly when it is realized. -/
theorem fullInverse_mulVec_signSum_pos {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < (fullInverse J *ᵥ (fun e => (signSum Z (∏ j, Q j ^ (e j).val) : ℚ))) σ ↔
      ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = σ j := by
  rw [fullInverse_mulVec_signSum]
  simp only [Nat.cast_pos, signCount_pos]

end TauCeti.SignDetermination
