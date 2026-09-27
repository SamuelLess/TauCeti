/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Square roots in the complexification of a real closed field

The usual algebraic square-root formula uses only square roots of nonnegative
elements of the base field. No completeness or Archimedean property is used.

Use `open scoped TauCeti.RealClosure` to synthesize the field instance on
`QuadraticAlgebra R (-1) 0` outside this namespace. The scope supplies
`Fact (¬ IsSquare (-1 : R))` from `IsSemireal R`, which activates Mathlib's
quadratic-algebra field instance.
-/

public section

namespace TauCeti.RealClosure

scoped instance {R : Type*} [Field R] [IsSemireal R] : Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

theorem exists_nonneg_sq {a : R} (ha : 0 ≤ a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, hr⟩ := IsRealClosed.exists_eq_pow_of_nonneg ha (n := 2) (by decide)
  exact ⟨|r|, abs_nonneg r, by simpa using hr.symm⟩

/-- Every element of `R[i]` is a square when `R` is real closed. -/
theorem complex_isSquare (z : QuadraticAlgebra R (-1) 0) : IsSquare z := by
  by_cases him : z.im = 0
  · rcases IsRealClosed.isSquare_or_isSquare_neg z.re with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨⟨r, 0⟩, ?_⟩
      ext <;> simp [him, hr]
    · refine ⟨⟨0, r⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_mul]
        linear_combination -hr
      · simp [him]
  · obtain ⟨m, hm0, hm⟩ := exists_nonneg_sq
      (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))
    have hpos : 0 < (m + z.re) / 2 := by
      have : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
      have : -z.re < m := by nlinarith
      exact div_pos (by linarith) (by norm_num)
    obtain ⟨s, hs0, hs⟩ := exists_nonneg_sq hpos.le
    have hspos : 0 < s := lt_of_le_of_ne hs0 (by intro h; subst s; simp at hs; linarith)
    have hs2 : 2 * s ^ 2 = m + z.re := by linarith
    refine ⟨⟨s, z.im / (2 * s)⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul]
      field_simp
      linear_combination -(2 * s ^ 2 + m - z.re) * hs2 - hm
    · simp only [QuadraticAlgebra.im_mul]
      field_simp
      ring

end TauCeti.RealClosure
