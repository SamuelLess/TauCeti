/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.OrderedSubfield
public import TauCeti.FieldTheory.RealClosure.OddExtension
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Existence of ordered algebraic real closures

A maximal ordered intermediate field of an algebraic closure is closed under
positive square roots and has a root of every odd-degree polynomial. Both
extension steps preserve the prescribed base order.
-/

public section

universe u

namespace RealClosure

open Polynomial

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] [Algebra K L] [IsAlgClosed L]

/-- A maximal ordered intermediate field of an algebraically closed field is real closed. -/
theorem OrderedSubfield.isRealClosed (P : OrderedSubfield K L) (hP : IsMax P) :
    IsRealClosed P.field := by
  let := P.order
  have := P.ordered
  apply IsRealClosed.of_linearOrderedField
  · intro a ha
    by_contra hn
    have : Fact (¬ IsSquare a) := ⟨hn⟩
    let E := QuadraticAlgebra P.field a 0
    obtain ⟨o, ho, hf⟩ := exists_quadratic_order ha
    let := o
    have := ho
    let f : E →ₐ[P.field] L := IsAlgClosed.lift
    let y : E := QuadraticAlgebra.omega
    have hy := P.mem_of_maximal hP f hf y
    apply hn
    refine ⟨⟨f y, hy⟩, ?_⟩
    apply Subtype.ext
    change (a : L) = f y * f y
    rw [← map_mul]
    have hy2 : y * y = algebraMap P.field E a := by
      simpa only [map_zero, zero_mul, add_zero] using
        (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (a := a) (b := 0))
    rw [hy2, f.commutes]
    rfl
  · intro p hp
    obtain ⟨q, hq, hqodd, hqp⟩ := exists_odd_factor p hp
    have : Fact (Irreducible q) := ⟨hq⟩
    have : FiniteDimensional P.field (AdjoinRoot q) := (AdjoinRoot.powerBasis hq.ne_zero).finite
    obtain ⟨o, ho, hf⟩ := exists_odd_order q hqodd
    let := o
    have := ho
    let f : AdjoinRoot q →ₐ[P.field] L := IsAlgClosed.lift
    have hy := P.mem_of_maximal hP f hf (AdjoinRoot.root q)
    let y : P.field := ⟨f (AdjoinRoot.root q), hy⟩
    refine ⟨y, ?_⟩
    have hpval : aeval (AdjoinRoot.root q) p = 0 := by
      rw [AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr hqp
    have hpL : aeval (f (AdjoinRoot.root q)) p = 0 := by
      rw [aeval_algHom_apply, hpval, map_zero]
    apply (algebraMap P.field L).injective
    rw [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact hpL

/-- Every ordered field has an algebraic real closed extension with an order
extending its given order, realized inside its algebraic closure. -/
theorem exists_intermediateField :
    ∃ F : IntermediateField K (AlgebraicClosure K), ∃ o : LinearOrder F,
      letI := o
      IsStrictOrderedRing F ∧ IsRealClosed F ∧ StrictMono (algebraMap K F) := by
  obtain ⟨P, hP⟩ := OrderedSubfield.exists_maximal (K := K) (L := AlgebraicClosure K)
  exact ⟨P.field, P.order, P.ordered, P.isRealClosed hP, P.base_strictMono⟩

/-- An ordered algebraic real closure exists in the universe of the base field.
The algebraicity assertion uses the algebra induced by the supplied embedding. -/
theorem exists_ordered_extension (K : Type u) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    ∃ (R : Type u) (field : Field R) (order : LinearOrder R),
      letI : Field R := field
      letI : LinearOrder R := order
      IsStrictOrderedRing R ∧ IsRealClosed R ∧
        ∃ ι : K →+* R, StrictMono ι ∧
          (letI : Algebra K R := ι.toAlgebra
           Algebra.IsAlgebraic K R) := by
  obtain ⟨F, o, ho, hr, hm⟩ := exists_intermediateField (K := K)
  refine ⟨F, F.toField, o, ho, hr, algebraMap K F, hm, ?_⟩
  rw [toAlgebra_algebraMap]
  infer_instance

end RealClosure
