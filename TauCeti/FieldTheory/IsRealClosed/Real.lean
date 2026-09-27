/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # The real numbers form a real closed field -/

public section

/-- A concrete model of the abstract axioms, using only Mathlib's real-analysis APIs. -/
instance : IsRealClosed ℝ := by
  apply IsRealClosed.of_linearOrderedField
  · intro x hx
    exact ⟨Real.sqrt x, by simpa only [pow_two] using (Real.sq_sqrt hx).symm⟩
  · intro p hp
    by_contra h
    have hleft : ∀ y, p.IsRoot y → y < 0 := fun y hy => (h ⟨y, hy⟩).elim
    have hright : ∀ y, p.IsRoot y → 0 < y := fun y hy => (h ⟨y, hy⟩).elim
    have hsign : Int.negOnePow (p.natDegree : ℤ) = -1 :=
      Int.negOnePow_odd _ (by exact_mod_cast hp)
    rcases le_total 0 p.leadingCoeff with hlc | hlc
    · have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hleft hlc
      have hneg := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        hright hlc
      rw [hsign] at hneg
      norm_num at hneg
      linarith
    · have hneg := Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hleft hlc
      have hpos := Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
        hright hlc
      rw [hsign] at hpos
      norm_num at hpos
      linarith
