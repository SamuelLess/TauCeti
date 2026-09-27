/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Fintype.Card

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
theorem fiberCount_pos (obs : X → S) (σ : S) : 0 < fiberCount obs σ ↔ ∃ x, obs x = σ := by
  simp [fiberCount, Finset.card_pos, Finset.nonempty_iff_ne_empty]

/-- An injective observation map gives multiplicity one precisely on its range. -/
theorem fiberCount_of_injective (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    fiberCount obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  classical
  by_cases h : ∃ x, obs x = σ
  · obtain ⟨x, hx⟩ := h
    have hf : Finset.univ.filter (fun y => obs y = σ) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hy => hinj (hy.trans hx.symm), fun hy => hy ▸ hx⟩
    have hex : ∃ y, obs y = σ := ⟨x, hx⟩
    simp only [fiberCount, hf, Finset.card_singleton, ite_eq_left hex]
  · have hf : Finset.univ.filter (fun y => obs y = σ) = ∅ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hy => h ⟨y, hy⟩
    simp only [fiberCount, hf, Finset.card_empty, ite_eq_right h]

/-- Multiplicity is the cardinality of the corresponding fiber. -/
theorem fiberCount_eq_card_filter (obs : X → S) (σ : S) :
    fiberCount obs σ = (Finset.univ.filter (fun x => obs x = σ)).card := (rfl)

end TauCeti
