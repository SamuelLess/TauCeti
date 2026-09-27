/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.PrimitiveElement
import TauCeti.Algebra.Polynomial.QuadraticDiscriminant
import Mathlib.FieldTheory.Minpoly.Finite

/-! # Finite extensions of an abstract real closed field -/

public section

namespace TauCeti.RealClosure

open Polynomial Module

variable {R E : Type*} [Field R] [IsRealClosed R] [Field E] [Algebra R E]
    [FiniteDimensional R E]

/-- An odd-degree finite extension of a real closed field is trivial. -/
theorem finrank_eq_one_of_odd (h : Odd (finrank R E)) : finrank R E = 1 := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element R E
  have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq R x).mp hx
  obtain ⟨a, ha⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (hdeg ▸ h)
  rw [← hdeg]
  exact natDegree_eq_of_degree_eq_some
    (degree_eq_one_of_irreducible_of_root (minpoly.irreducible (IsIntegral.of_finite R x)) ha)

section Quadratic

variable {K L : Type*} [Field K] [NeZero (2 : K)]

/-- A square-closed field of characteristic different from two has no quadratic extension. -/
theorem finrank_ne_two_of_isSquare [Field L] [Algebra K L]
    [FiniteDimensional K L] (hsq : ∀ x : K, IsSquare x) : finrank K L ≠ 2 := by
  intro htwo
  have hsurj : Function.Surjective (Algebra.linearMap K L) := by
    intro x
    apply minpoly.natDegree_eq_one_iff.mp
    have hpos := minpoly.natDegree_pos (IsIntegral.of_finite K x)
    have hle := (minpoly.natDegree_le x).trans_eq htwo
    by_contra hne
    have hdeg : (minpoly K x).natDegree = 2 := by omega
    obtain ⟨a, ha⟩ := exists_root_of_isSquare_discrim hdeg (hsq _)
    have hone : (minpoly K x).natDegree = 1 := natDegree_eq_of_degree_eq_some
      (degree_eq_one_of_irreducible_of_root (minpoly.irreducible (IsIntegral.of_finite K x)) ha)
    omega
  have := LinearMap.finrank_le_finrank_of_surjective hsurj
  simp only [htwo, finrank_self] at this
  omega

end Quadratic

end TauCeti.RealClosure
