/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PeriodAction
import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The trace reduction to the ambient space of binary forms

Let `K` be a field, `w` an even natural number and `ξ ∈ K[ℳₙ]` an element satisfying Popa and
Zagier's exchange relations (B). On the space `V_w` of binary forms of degree `w`, the action of
`ξ` maps each of the subspaces `A = ker (1 + S)` and `B = ker (1 + U + U²)`, with `U = T S`, into
the other. It therefore preserves both the period-polynomial space `W_w = A ∩ B` and `A + B`, and
its traces on the two agree. When `A + B = V_w`, this is Popa and Zagier's reduction
`tr(ξ | W_w) = tr(ξ | V_w)` of the trace on period polynomials to the trace on all binary forms.

## Main results

* `TraceFormulaMatrixModule.ExchangeRelations.trace_periodActionRestrict_eq_trace_restrict_sup`:
  the trace of `ξ` on `W_w = A ∩ B` is its trace on `A + B`.
* `TraceFormulaMatrixModule.ExchangeRelations.trace_periodActionRestrict_eq_trace`: if
  `A + B = V_w`, then the trace of `ξ` on `W_w` is its trace on `V_w`.

## Implementation notes

Popa and Zagier prove `A + B = V_w` for `w > 0` from a nondegenerate `Γ`-invariant inner product
on `V_w`: the orthogonal complement of `A + B` is the space of `Γ`-invariants, which is zero for
`w > 0`. That input is not proved here: it enters
`TauCeti.TraceFormulaMatrixModule.ExchangeRelations.trace_periodActionRestrict_eq_trace` as the
hypothesis `Codisjoint A B`. For `w = 0` it fails when `2` and `3` are invertible, since then
`A = B = 0`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2, Proposition 3.
-/

public section

open MonoidAlgebra MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {K : Type*} [Field K] {n : ℤ} {w : ℕ}

/-- The traces of the restrictions of `f` to equal submodules agree. -/
private theorem trace_restrict_congr {V : Type*} [AddCommGroup V] [Module K V]
    {p q : Submodule K V} (hpq : p = q) (f : V →ₗ[K] V) (hp : ∀ x ∈ p, f x ∈ p)
    (hq : ∀ x ∈ q, f x ∈ q) :
    LinearMap.trace K p (f.restrict hp) = LinearMap.trace K q (f.restrict hq) := by
  subst hpq
  rfl

/-- The trace of `ξ` on the period polynomials, computed on `ker (1 + S) ⊓ ker (1 + U + U²)`. -/
private theorem ExchangeRelations.trace_periodActionRestrict_eq_trace_restrict_inf (hw : Even w)
    {ξ : K[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations K n ξ) :
    LinearMap.trace K (periodPolynomials K w) (hξ.periodActionRestrict hw) =
      LinearMap.trace K
        ↥(LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊓
          LinearMap.ker
            (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
              binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2))
        ((periodAction (R := K) hw ξ).restrict fun _ hP ↦
          ⟨hξ.periodAction_mem_ker_one_add_S hw hP.2,
            hξ.periodAction_mem_ker_one_add_U_add_U_sq hw hP.1⟩) := by
  have h : hξ.periodActionRestrict hw = (periodAction (R := K) hw ξ).restrict
      fun _ hP ↦ hξ.periodAction_mem_periodPolynomials hw hP :=
    LinearMap.ext fun P ↦ Subtype.ext (hξ.coe_periodActionRestrict_apply hw P)
  rw [h]
  exact trace_restrict_congr periodPolynomials_def _ _ _

/-- **Trace reduction to `A + B`** (Popa–Zagier, Proposition 3, proof): for even `w`, the action of
an element `ξ` satisfying the exchange relations has the same trace on the period polynomials
`W_w = ker (1 + S) ∩ ker (1 + U + U²)` as on `ker (1 + S) + ker (1 + U + U²)`, where `U = T S`. -/
theorem ExchangeRelations.trace_periodActionRestrict_eq_trace_restrict_sup (hw : Even w)
    {ξ : K[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations K n ξ) :
    LinearMap.trace K (periodPolynomials K w) (hξ.periodActionRestrict hw) =
      LinearMap.trace K
        ↥(LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊔
          LinearMap.ker
            (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
              binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2))
        ((periodAction (R := K) hw ξ).restrict fun _ hP ↦
          (sup_le (fun _ hP ↦ Submodule.mem_sup_right
              (hξ.periodAction_mem_ker_one_add_U_add_U_sq hw hP))
            (fun _ hP ↦ Submodule.mem_sup_left (hξ.periodAction_mem_ker_one_add_S hw hP)) :
            _ ≤ Submodule.comap (periodAction (R := K) hw ξ) _) hP) := by
  rw [hξ.trace_periodActionRestrict_eq_trace_restrict_inf hw]
  exact LinearMap.trace_restrict_inf_eq_trace_restrict_sup
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_U_add_U_sq hw)
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_S hw)

/-- **The trace reduction** (Popa–Zagier, Proposition 3): for even `w`, if
`ker (1 + S) + ker (1 + U + U²)` is all of `V_w`, where `U = T S`, then the action of an element `ξ`
satisfying the exchange relations has the same trace on the period polynomials `W_w` as on the
binary forms `V_w`. -/
theorem ExchangeRelations.trace_periodActionRestrict_eq_trace (hw : Even w)
    {ξ : K[TraceFormulaMatrixModule n]} (hξ : ExchangeRelations K n ξ)
    (hAB : Codisjoint (LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))))
      (LinearMap.ker
        (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
          binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2))) :
    LinearMap.trace K (periodPolynomials K w) (hξ.periodActionRestrict hw) =
      LinearMap.trace K (homogeneousSubmodule (Fin 2) K w) (periodAction (R := K) hw ξ) := by
  rw [hξ.trace_periodActionRestrict_eq_trace_restrict_inf hw]
  exact LinearMap.trace_restrict_inf_eq_trace hAB
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_U_add_U_sq hw)
    (fun _ ↦ hξ.periodAction_mem_ker_one_add_S hw)

end TauCeti.TraceFormulaMatrixModule
