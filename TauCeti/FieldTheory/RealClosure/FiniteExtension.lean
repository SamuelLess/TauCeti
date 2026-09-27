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
public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Tactic.NormNum

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

/-- A quadratic polynomial whose discriminant is a square has a root. -/
theorem _root_.Polynomial.exists_root_of_isSquare_discrim {p : K[X]} (hp : p.natDegree = 2)
    (hsq : IsSquare (discrim (p.coeff 2) (p.coeff 1) (p.coeff 0))) :
    ∃ x, p.IsRoot x := by
  have hlead : p.coeff 2 ≠ 0 := by
    rw [← hp]
    have hpos : 0 < p.natDegree := by omega
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hpos)
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero hlead hsq
  refine ⟨x, ?_⟩
  rw [Polynomial.IsRoot, eq_quadratic_of_degree_le_two
    (natDegree_le_iff_degree_le.mp hp.le)]
  simpa [pow_two] using hx

/-- A quadratic polynomial has a root in a field in which every element is a square. -/
theorem quadratic_has_root (hsq : ∀ x : K, IsSquare x) {p : K[X]}
    (hp : p.natDegree = 2) : ∃ x, p.IsRoot x :=
  exists_root_of_isSquare_discrim hp (hsq _)

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
    obtain ⟨a, ha⟩ := quadratic_has_root hsq hdeg
    have hone : (minpoly K x).natDegree = 1 := natDegree_eq_of_degree_eq_some
      (degree_eq_one_of_irreducible_of_root (minpoly.irreducible (IsIntegral.of_finite K x)) ha)
    omega
  have := LinearMap.finrank_le_finrank_of_surjective hsurj
  simp only [htwo, finrank_self] at this
  omega

end Quadratic

end TauCeti.RealClosure
