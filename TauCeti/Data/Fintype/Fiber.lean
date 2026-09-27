/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Multiplicities in a finite family

`fiberCount f y` counts the indices at which a finite family `f` takes the value `y`.
-/

public section

namespace TauCeti

variable {X S : Type*} [Fintype X] [DecidableEq S]

/-- Multiplicity of a value in a finite family. -/
def fiberCount (obs : X → S) (σ : S) : ℕ :=
  (Finset.univ.filter (fun x => obs x = σ)).card

/-- Positive multiplicity means the value occurs. -/
@[simp] theorem fiberCount_pos (obs : X → S) (σ : S) : 0 < fiberCount obs σ ↔ ∃ x, obs x = σ := by
  simp [fiberCount, Finset.card_pos, Finset.nonempty_iff_ne_empty]

/-- An injective observation map gives multiplicity one precisely on its range. -/
theorem fiberCount_of_injective (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    fiberCount obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨x, rfl⟩ := h
    simp only [fiberCount, hinj.eq_iff]
    exact Finset.card_eq_one.mpr ⟨x, by ext y; simp⟩
  · simpa [fiberCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_exists] using h

/-- Multiplicity is the cardinality of the corresponding fiber. -/
theorem fiberCount_eq_card_filter (obs : X → S) (σ : S) :
    fiberCount obs σ = (Finset.univ.filter (fun x => obs x = σ)).card := (rfl)

/-- Summing weights over a complete, injective list of candidate values equals summing
those weights over the original family with their multiplicities. -/
theorem sum_mul_fiberCount {C K : Type*} [Fintype C] [Semiring K]
    (obs : X → S) (columns : C → S) (hinj : Function.Injective columns)
    (cover : ∀ x, ∃ c, columns c = obs x) (weight : S → K) :
    ∑ c, weight (columns c) * (fiberCount obs (columns c) : K) =
      ∑ x, weight (obs x) := by
  classical
  simp only [fiberCount_eq_card_filter, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
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

end TauCeti
