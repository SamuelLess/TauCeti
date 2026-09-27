/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! # Finite sign determination

Counts refer to an actual finite family of observations, independently of a
proposed solution of a moment system. A reduced system determines those counts
only when its candidate columns cover every observation.
-/

public section

open scoped BigOperators Matrix

namespace SignDetermination

variable {X S C I : Type*} [Fintype X] [Fintype C] [Fintype I]
    [DecidableEq S] [DecidableEq C]

/-- Multiplicity of a proposed sign condition in a finite observation family. -/
def count (obs : X → S) (σ : S) : ℚ :=
  ((Finset.univ.filter (fun x => obs x = σ)).card : ℚ)

/-- The multiplicity counts observations, not distinct sign patterns. -/
theorem count_eq_sum (obs : X → S) (σ : S) :
    count obs σ = ∑ x, if obs x = σ then (1 : ℚ) else 0 := by
  simp [count, Finset.sum_boole]

/-- Positive multiplicity means the condition is actually realized. -/
theorem count_pos (obs : X → S) (σ : S) : 0 < count obs σ ↔ ∃ x, obs x = σ := by
  simp [count, Finset.card_pos, Finset.nonempty_iff_ne_empty]

/-- Every actual count is a nonnegative integer. -/
theorem count_integral (obs : X → S) (σ : S) : ∃ n : ℕ, count obs σ = n :=
  ⟨_, rfl⟩

omit [Fintype I] [DecidableEq C] in
/-- Complete candidate columns satisfy the moment equations. -/
theorem count_moments (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → ℚ) :
    (Matrix.of fun i c => weight i (columns c)) *ᵥ (fun c => count obs (columns c)) =
      fun i => ∑ x, weight i (obs x) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, count_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨c, hc⟩ := cover x
  rw [Finset.sum_eq_single c]
  · simp [hc]
  · intro d _ hdc
    have hne : obs x ≠ columns d := by
      intro he
      exact hdc (hinj (he.symm.trans hc.symm))
    simp [hne]
  · simp

omit [Fintype I] [DecidableEq C] in
/-- The same moment identity over integers, before any inverse introduces
rational coefficients. -/
theorem count_moments_int (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → ℤ) :
    (Matrix.of fun i c => weight i (columns c)) *ᵥ
        (fun c => ((Finset.univ.filter (fun x => obs x = columns c)).card : ℤ)) =
      fun i => ∑ x, weight i (obs x) := by
  funext i
  have hi := congrFun (count_moments obs columns hinj cover
    (fun i σ => (weight i σ : ℚ))) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, count] at hi ⊢
  exact_mod_cast hi

/-- An independently checked left inverse gives uniqueness on the candidate
columns. Coverage is an essential separate premise, not a consequence of this
matrix identity. -/
theorem solve_counts (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → ℚ) (A : Matrix C I ℚ)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C ℚ) = 1) (proposed : C → ℚ)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) :
    proposed = fun c => count obs (columns c) := by
  have hm := count_moments obs columns hinj cover weight
  have he := congrArg (fun v => A *ᵥ v) (hsolve.trans hm.symm)
  simpa only [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec] using he

omit [DecidableEq S] in
/-- Zero pruning keeps exactly the realizable candidate conditions. -/
theorem support_exact (obs : X → S) (columns : C → S)
    (hinj : Function.Injective columns) (cover : ∀ x, ∃ c, columns c = obs x)
    (weight : I → S → ℚ) (A : Matrix C I ℚ)
    (hA : (A * (Matrix.of fun i c => weight i (columns c)) : Matrix C C ℚ) = 1) (proposed : C → ℚ)
    (hsolve : (Matrix.of fun i c => weight i (columns c)) *ᵥ proposed =
      fun i => ∑ x, weight i (obs x)) (c : C) :
    0 < proposed c ↔ ∃ x, obs x = columns c := by
  classical
  rw [solve_counts obs columns hinj cover weight A hA proposed hsolve]
  exact count_pos obs (columns c)

omit [Fintype X] in
/-- Complete child supports cover every parent observation in their Cartesian
product. This implication precedes the parent's reduced solve. -/
theorem product_covers {L R A B : Type*} (left : X → L) (right : X → R)
    (lc : A → L) (rc : B → R)
    (hl : ∀ x, ∃ a, lc a = left x) (hr : ∀ x, ∃ b, rc b = right x) :
    ∀ x, ∃ ab : A × B, (lc ab.1, rc ab.2) = (left x, right x) := by
  intro x
  obtain ⟨a, ha⟩ := hl x
  obtain ⟨b, hb⟩ := hr x
  exact ⟨(a, b), by simp [ha, hb]⟩

/-- An injective observation map gives multiplicity one precisely on its range. -/
theorem count_of_injective (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    count obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  classical
  by_cases h : ∃ x, obs x = σ
  · obtain ⟨x, hx⟩ := h
    have hf : Finset.univ.filter (fun y => obs y = σ) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hy => hinj (hy.trans hx.symm), fun hy => hy ▸ hx⟩
    have hex : ∃ y, obs y = σ := ⟨x, hx⟩
    simp only [count, hf, Finset.card_singleton, Nat.cast_one, ite_eq_left hex]
  · have hf : Finset.univ.filter (fun y => obs y = σ) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hy => h ⟨y, hy⟩
    simp only [count, hf, Finset.card_empty, Nat.cast_zero, ite_eq_right h]

/-- Coefficients of the three Lagrange indicator polynomials on `{-1,0,1}`. -/
def inverseCoeff (s : SignType) (e : Fin 3) : ℚ :=
  match s with
  | .zero => if e = 0 then 1 else if e = 2 then -1 else 0
  | .neg => if e = 1 then -1/2 else if e = 2 then 1/2 else 0
  | .pos => if e = 1 then 1/2 else if e = 2 then 1/2 else 0

/-- The one-coordinate moment matrix has an explicit rational left inverse. -/
theorem inverseCoeff_sum (s t : SignType) :
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

/-- The tensor inverse works for every finite number of sign queries,
including zero. This is the uniqueness fact a full-table solver needs. -/
theorem full_left_inverse : fullInverse J * fullMatrix J = 1 := by
  classical
  ext σ τ
  rw [Matrix.mul_apply, Matrix.one_apply]
  change (∑ e : J → Fin 3, (∏ j, inverseCoeff (σ j) (e j)) *
    ∏ j, (τ j : ℚ) ^ (e j).val) = _
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : J) (e : Fin 3) => inverseCoeff (σ j) e * (τ j : ℚ) ^ e.val)]
  simp only [inverseCoeff_sum]
  by_cases heq : σ = τ
  · subst τ
    simp
  · obtain ⟨j, hj⟩ : ∃ j, σ j ≠ τ j := by
      by_contra hn
      push Not at hn
      exact heq (funext hn)
    rw [ite_eq_right heq]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- Equal finite dimensions turn the explicit left inverse into a right inverse. -/
theorem full_right_inverse : fullMatrix J * fullInverse J = 1 := by
  classical
  apply (Matrix.mul_eq_one_comm_of_card_eq (J → SignType) (J → Fin 3) ℚ
    (A := fullInverse J) (B := fullMatrix J) ?_).mp
    (full_left_inverse J)
  simp only [Fintype.card_fun]
  have hs : Fintype.card SignType = Fintype.card (Fin 3) := by decide
  rw [hs]

/-- Explicit inversion of all ternary moments recovers each actual sign count. -/
theorem full_recovery (obs : X → (J → SignType)) :
    fullInverse J *ᵥ (fun e => ∑ x, ∏ j, (obs x j : ℚ) ^ (e j).val) =
      fun σ => count obs σ := by
  have hm := count_moments obs id Function.injective_id (fun x => ⟨obs x, rfl⟩)
    (fun (e : J → Fin 3) σ => ∏ j, (σ j : ℚ) ^ (e j).val)
  change fullMatrix J *ᵥ (fun σ => count obs σ) = _ at hm
  rw [← hm, Matrix.mulVec_mulVec, full_left_inverse, Matrix.one_mulVec]

end SignDetermination
