/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic.NormNum

/-! # Finite sign determination

Counts refer to an actual finite family of observations, independently of a
proposed solution of a moment system. `eq_occCount` recovers multiplicities on
candidate columns only when they cover every observation. `fullInverse_mulVec` gives
an explicit inverse for all ternary sign conditions.

Here `X` indexes observations, `S` is the space of sign conditions, `C` indexes
candidate columns, and `I` indexes moment rows.

## References

For the full ternary moment matrix and finite sign determination, see
S. Basu, R. Pollack, M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, 2nd ed.](https://doi.org/10.1007/3-540-33099-2),
Chapter 10, and C. Cohen, A. Mahboubi,
[Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination]
(https://doi.org/10.2168/LMCS-8(1:2)2012), LMCS 8(1), 2012.
-/

public section

open scoped Matrix

namespace TauCeti.SignDetermination

variable {X S C I : Type*} [Fintype X] [Fintype C] [Fintype I]
    [DecidableEq C]

omit [Fintype I] [DecidableEq C] in
/-- Complete candidate columns satisfy the moment equations. -/
theorem mulVec_occCount {K : Type*} [Semiring K] (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) :
    (Matrix.of fun i c => weight i (columns c)) *ᵥ (fun c => (occCount obs (columns c) : K)) =
      fun i => ∑ x, weight i (obs x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact sum_mul_occCount obs columns hinj cover (weight i)

/-- An independently checked left inverse gives uniqueness on the candidate
columns. Coverage is an essential separate premise, not a consequence of this
matrix identity. -/
theorem eq_occCount {K : Type*} [Semiring K] (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) (A : Matrix C I K)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C K) = 1) (proposed : C → K)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) :
    proposed = fun c => (occCount obs (columns c) : K) := by
  have hm := mulVec_occCount obs columns hinj cover weight
  have he := congrArg (fun v => A *ᵥ v) (hsolve.trans hm.symm)
  simpa only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec] using he

/-- With a left inverse and complete columns, a solved entry is positive exactly
when its candidate condition occurs among the observations. -/
theorem solution_pos_iff {K : Type*} [Semiring K] [PartialOrder K] [IsOrderedRing K] [Nontrivial K]
    (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → K) (A : Matrix C I K)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C K) = 1) (proposed : C → K)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) (c : C) :
    0 < proposed c ↔ ∃ x, obs x = columns c := by
  classical
  rw [eq_occCount obs columns hinj cover weight A hA proposed hsolve]
  simpa only [Nat.cast_pos] using occCount_pos obs (columns c)

/-- Coefficients of the three Lagrange indicator polynomials on `{-1,0,1}`. -/
def inverseCoeff (s : SignType) (e : Fin 3) : ℚ :=
  match s with
  | .zero => if e = 0 then 1 else if e = 2 then -1 else 0
  | .neg => if e = 1 then -1/2 else if e = 2 then 1/2 else 0
  | .pos => if e = 1 then 1/2 else if e = 2 then 1/2 else 0

@[simp, grind =]
theorem inverseCoeff_zero (e : Fin 3) :
    inverseCoeff 0 e = if e = 0 then 1 else if e = 2 then -1 else 0 := (rfl)

@[simp, grind =]
theorem inverseCoeff_neg_one (e : Fin 3) :
    inverseCoeff (-1) e = if e = 1 then -1/2 else if e = 2 then 1/2 else 0 := (rfl)

@[simp, grind =]
theorem inverseCoeff_one (e : Fin 3) :
    inverseCoeff 1 e = if e = 1 then 1/2 else if e = 2 then 1/2 else 0 := (rfl)

/-- The one-coordinate moment matrix has an explicit rational left inverse. -/
theorem sum_inverseCoeff_mul_pow (s t : SignType) :
    ∑ e : Fin 3, inverseCoeff s e * (t : ℚ) ^ e.val = if s = t then 1 else 0 := by
  cases s <;> cases t <;> norm_num [Fin.sum_univ_three, inverseCoeff]

variable (J : Type*) [Fintype J] [DecidableEq J]

/-- The full ternary moment matrix has one row per exponent word and one
column per sign word. An empty coordinate set gives the one-by-one matrix. -/
def fullMatrix : Matrix (J → Fin 3) (J → SignType) ℚ :=
  Matrix.of fun e σ => ∏ j, (σ j : ℚ) ^ (e j).val

/-- Tensor product of the one-coordinate inverse coefficients. -/
def fullInverse : Matrix (J → SignType) (J → Fin 3) ℚ :=
  Matrix.of fun σ e => ∏ j, inverseCoeff (σ j) (e j)

omit [DecidableEq J] in
@[simp, grind =]
theorem fullMatrix_apply (e : J → Fin 3) (σ : J → SignType) :
    fullMatrix J e σ = ∏ j, (σ j : ℚ) ^ (e j).val := (rfl)

omit [DecidableEq J] in
@[simp, grind =]
theorem fullInverse_apply (σ : J → SignType) (e : J → Fin 3) :
    fullInverse J σ e = ∏ j, inverseCoeff (σ j) (e j) := (rfl)

/-- The tensor inverse works for every finite number of sign queries,
including zero. This is the uniqueness fact a full-table solver needs. -/
@[simp, grind =]
theorem fullInverse_mul_fullMatrix : fullInverse J * fullMatrix J = 1 := by
  classical
  ext σ τ
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [fullInverse_apply, fullMatrix_apply]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : J) (e : Fin 3) => inverseCoeff (σ j) e * (τ j : ℚ) ^ e.val)]
  simp only [sum_inverseCoeff_mul_pow]
  by_cases heq : σ = τ
  · subst τ
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp heq
    rw [ite_eq_right heq]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The tensor inverse is also a right inverse of the full ternary moment matrix. -/
@[simp, grind =]
theorem fullMatrix_mul_fullInverse : fullMatrix J * fullInverse J = 1 := by
  classical
  apply (Matrix.mul_eq_one_comm_of_card_eq (J → SignType) (J → Fin 3) ℚ
    (A := fullInverse J) (B := fullMatrix J) ?_).mp
    (fullInverse_mul_fullMatrix J)
  simp only [Fintype.card_fun]
  have hs : Fintype.card SignType = Fintype.card (Fin 3) := by decide
  rw [hs]

/-- The full sign matrix maps the actual multiplicities to the sign moments. -/
theorem fullMatrix_mulVec_occCount (obs : X → (J → SignType)) :
    fullMatrix J *ᵥ (fun σ => (occCount obs σ : ℚ)) =
      fun e => ∑ x, ∏ j, (obs x j : ℚ) ^ (e j).val := by
  simpa only [fullMatrix, id_eq] using
    mulVec_occCount obs id Function.injective_id (fun x => ⟨obs x, rfl⟩)
      (fun (e : J → Fin 3) σ => ∏ j, (σ j : ℚ) ^ (e j).val)

/-- Explicit inversion of all ternary moments recovers each actual sign count. -/
theorem fullInverse_mulVec (obs : X → (J → SignType)) :
    fullInverse J *ᵥ (fun e => ∑ x, ∏ j, (obs x j : ℚ) ^ (e j).val) =
      fun σ => (occCount obs σ : ℚ) := by
  rw [← fullMatrix_mulVec_occCount, Matrix.mulVec_mulVec,
    fullInverse_mul_fullMatrix, Matrix.one_mulVec]

end TauCeti.SignDetermination
