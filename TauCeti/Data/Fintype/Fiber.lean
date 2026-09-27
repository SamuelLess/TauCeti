/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Occurrence counts in finite families

`occCount f y` counts the indices at which a family `f` takes the value `y`.
For an infinite fiber its value is zero, following the convention of `Nat.card`.
The finite-family API includes positivity and weighted sums.
-/

public section

namespace TauCeti

variable {X S : Type*}

/-- The cardinality of a fiber, counting occurrences of a value in a family. -/
noncomputable def occCount (obs : X → S) (σ : S) : ℕ := Nat.card {x // obs x = σ}

/-- Occurrence counts are natural cardinalities of fibers. -/
theorem occCount_def (obs : X → S) (σ : S) :
    occCount obs σ = Nat.card {x // obs x = σ} := (rfl)

/-- Multiplicity is the cardinality of the corresponding finite fiber. -/
theorem occCount_eq_card_filter [Fintype X] [DecidableEq S] (obs : X → S) (σ : S) :
    occCount obs σ = (Finset.univ.filter (fun x => obs x = σ)).card := by
  rw [occCount_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Positive multiplicity means the value occurs. -/
@[simp, grind =]
theorem occCount_pos [Finite X] (obs : X → S) (σ : S) : 0 < occCount obs σ ↔ ∃ x, obs x = σ := by
  classical
  let := Fintype.ofFinite X
  simp [occCount_eq_card_filter, Finset.card_pos, Finset.nonempty_iff_ne_empty]

open scoped Classical in
/-- An injective observation map gives multiplicity one precisely on its range. -/
@[simp]
theorem occCount_of_injective (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    occCount obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  split_ifs with h
  · let _ : Nonempty {x // obs x = σ} := ⟨⟨h.choose, h.choose_spec⟩⟩
    let _ : Subsingleton {x // obs x = σ} :=
      ⟨fun x y ↦ Subtype.ext (hinj (x.property.trans y.property.symm))⟩
    exact Nat.card_unique
  · rw [occCount_def, Nat.card_eq_zero]
    exact Or.inl ⟨fun x ↦ h ⟨x, x.property⟩⟩

/-- Summing weights on complete, injective candidate values equals summing over
the original family with multiplicity. -/
theorem sum_occCount_nsmul [Fintype X] {C K : Type*} [Fintype C] [AddCommMonoid K]
    (obs : X → S) (columns : C → S) (hinj : Function.Injective columns)
    (cover : ∀ x, ∃ c, columns c = obs x) (weight : S → K) :
    ∑ c, occCount obs (columns c) • weight (columns c) =
      ∑ x, weight (obs x) := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ)
    (t := Finset.univ.image columns) (g := obs) (fun x _ => by
      obtain ⟨c, hc⟩ := cover x
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩) weight
  rw [Finset.sum_image hinj.injOn] at h
  simpa only [Finset.sum_const, occCount_eq_card_filter] using h

end TauCeti
