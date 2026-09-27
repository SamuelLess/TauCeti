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
integer sum of signs on a specified finite set. `signSum_prod_pow` expresses
the sign sum of a product as a moment of these counts. `fullInverse_signSum` inverts
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
noncomputable def signEval {K : Type*} [Ring K] (x : R) : R[X] →*₀ K :=
  SignType.castHom.comp (signHom.comp (Polynomial.evalRingHom x).toMonoidWithZeroHom)

@[simp] theorem signEval_apply {K : Type*} [Ring K] (x : R) (p : R[X]) :
    signEval x p = (sign (p.eval x) : K) := (rfl)

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, signEval x.val p

/-- Sign sums are integer sums of pointwise polynomial signs. -/
@[simp] theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x : Z, (sign (p.eval x.val) : ℤ) := (rfl)

/-- The number of points realizing a specified polynomial sign condition. -/
noncomputable def signCount {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) : ℕ := by
  classical
  exact count (fun x : Z => fun j => sign ((Q j).eval x.val)) σ

omit [IsStrictOrderedRing R] in
/-- Polynomial sign counts are multiplicities in the finite family of pointwise signs. -/
theorem signCount_eq_count {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = count (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := by
  classical
  rfl

/-- Polynomial product sign sums are the moments of the observed sign words. -/
theorem signSum_product {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ x : Z, ∏ j, (sign ((Q j).eval x.val) : ℤ) ^ e j := by
  simp only [signSum, map_prod, map_pow, signEval_apply]

/-- The polynomial moment identity on any complete restricted column set and
any selected exponent rows. Exponents need not be bounded by two. -/
theorem restricted_moments {J C I : Type*} [Fintype J]
    [Fintype C] (Z : Finset R) (Q : J → R[X])
    (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x : Z, ∃ c, columns c = fun j => sign ((Q j).eval x.val)) :
    (Matrix.of fun i c => ∏ j, (columns c j : ℤ) ^ rows i j) *ᵥ
        (fun c => (signCount Z Q (columns c) : ℤ)) =
      fun i => signSum Z (∏ j, Q j ^ rows i j) := by
  classical
  simp_rw [signSum_product]
  exact count_moments _ columns hinj cover (fun i σ => ∏ j, (σ j : ℤ) ^ rows i j)

/-- All ternary moments determine the exact multiplicity of every sign pattern. -/
theorem fullInverse_signSum {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (signSum Z (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount Z Q σ : ℚ) := by
  simp_rw [signSum_product]
  simpa only [Int.cast_sum, Int.cast_prod, Int.cast_pow, signCount, SignType.intCast_cast] using
    fullInverse_mulVec J (fun x : Z => fun j => sign ((Q j).eval x.val))

/-- The integer BKR moment identity on a finite set of sample points. -/
theorem signSum_prod_pow {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) * (signCount Z Q σ : ℤ) := by
  classical
  exact (congrFun (restricted_moments Z Q id (fun (_ : Unit) => e)
    Function.injective_id (fun x => ⟨_, rfl⟩)) ()).symm

/-- The recovered sign pattern is positive exactly when it is realized. -/
theorem recovered_pos {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < (fullInverse J *ᵥ (fun e => (signSum Z (∏ j, Q j ^ (e j).val) : ℚ))) σ ↔
      ∃ x : Z, ∀ j, sign ((Q j).eval x.val) = σ j := by
  rw [fullInverse_signSum]
  simp only [Nat.cast_pos, signCount, count_pos, funext_iff]

end TauCeti.SignDetermination
