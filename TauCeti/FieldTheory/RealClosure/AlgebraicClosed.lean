/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.Galois
public import TauCeti.FieldTheory.RealClosure.Complexification
public import TauCeti.Algebra.Order.Ring.Ordering.Semireal
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic closedness of the complexification

Finite extensions are put inside a finite normal closure. The 2-group argument
then applies to the Galois group over a square-closed intermediate field.

## References

The algebraic argument uses a Sylow 2-subgroup of the Galois group; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Theorem 2.2.
-/

public section

namespace TauCeti.RealClosure

open Module IntermediateField

variable {R C L : Type*} [Field R] [IsRealClosed R] [Field C] [Algebra R C]
    [FiniteDimensional R C] [Field L] [Algebra R L] [Algebra C L]
    [IsScalarTower R C L] [FiniteDimensional C L]

include R in
/-- Every finite extension of a finite square-closed extension of a real
closed field is trivial. -/
theorem SquareClosed.finrank_eq_one (hsq : ∀ x : C, IsSquare x) :
    finrank C L = 1 := by
  let M := AlgebraicClosure L
  have : FiniteDimensional R L := FiniteDimensional.trans R C L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap R L).injective
  have : IsGalois R M := { }
  let N := normalClosure R L M
  let : Algebra C N := ((algebraMap L N).comp (algebraMap C L)).toAlgebra
  have : IsScalarTower C L N := .of_algebraMap_eq' rfl
  have : IsScalarTower R C N := .of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R L N, IsScalarTower.algebraMap_eq R C L]
    rfl)
  have hN : Module.finrank C N = 1 := SquareClosed.finrank_eq_one_of_isGalois (R := R) hsq
  exact Nat.eq_one_of_dvd_one (hN ▸ finrank_dvd_finrank_right C L N)

include R in
/-- A finite square-closed extension of a real closed field is algebraically closed. -/
theorem SquareClosed.isAlgClosed (hsq : ∀ x : C, IsSquare x) : IsAlgClosed C := by
  apply IsAlgClosed.of_exists_root
  intro p _ hp
  have : Fact (Irreducible p) := ⟨hp⟩
  have : FiniteDimensional C (AdjoinRoot p) :=
    (AdjoinRoot.powerBasis hp.ne_zero).finite
  have hdim := SquareClosed.finrank_eq_one (R := R) (L := AdjoinRoot p) hsq
  have hdeg : p.natDegree = 1 := by
    rwa [(AdjoinRoot.powerBasis hp.ne_zero).finrank] at hdim
  exact Polynomial.exists_root_of_degree_eq_one
    (by rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]; rfl)

/-- The complexification `R[i]` of a real closed field is algebraically closed. -/
theorem complex_isAlgClosed : IsAlgClosed (QuadraticAlgebra R (-1) 0) :=
  SquareClosed.isAlgClosed (R := R) complex_isSquare

end TauCeti.RealClosure
