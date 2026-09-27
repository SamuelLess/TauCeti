/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Kim Morrison
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Occurrence counts in finite families

`occCount f y` counts the indices at which a family `f` takes the value `y`.
For an infinite fiber its value is zero, following the convention of `Nat.card`.
The finite-family API includes positivity, weighted sums, and total multiplicity.
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
theorem occCount_of_injective [Finite X] (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    occCount obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  classical
  let := Fintype.ofFinite X
  split_ifs with h
  · obtain ⟨x, rfl⟩ := h
    simp only [occCount_eq_card_filter, hinj.eq_iff]
    exact Finset.card_eq_one.mpr ⟨x, by ext y; simp⟩
  · simpa [occCount_eq_card_filter, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff, not_exists] using h

/-- Summing weights on complete, injective candidate values equals summing over
the original family with multiplicity. -/
theorem sum_mul_occCount [Fintype X] {C K : Type*} [Fintype C] [Semiring K]
    (obs : X → S) (columns : C → S) (hinj : Function.Injective columns)
    (cover : ∀ x, ∃ c, columns c = obs x) (weight : S → K) :
    ∑ c, weight (columns c) * (occCount obs (columns c) : K) =
      ∑ x, weight (obs x) := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ)
    (t := Finset.univ.image columns) (g := obs) (fun x _ => by
      obtain ⟨c, hc⟩ := cover x
      exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩) weight
  rw [Finset.sum_image hinj.injOn] at h
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_comm,
    occCount_eq_card_filter] using h

/-- Counts over a finite set containing every observed value sum to the family size. -/
theorem sum_occCount_eq_card [Fintype X] (obs : X → S) {T : Finset S} (hT : ∀ x, obs x ∈ T) :
    ∑ σ ∈ T, occCount obs σ = Fintype.card X := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := obs) (t := T)
    fun x _ => hT x
  simpa only [Finset.card_univ, occCount_eq_card_filter] using h.symm

/-- The total multiplicity is the number of indices in the family. -/
theorem sum_occCount [Fintype X] [Fintype S] (obs : X → S) :
    ∑ σ, occCount obs σ = Fintype.card X :=
  sum_occCount_eq_card obs (fun _ => Finset.mem_univ _)

end TauCeti
