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
Occurrence counts regroup sums over a finite family by fibers: candidate values containing the
observed range can be weighted by their multiplicities instead of summing over every index.
-/

public section

open Finset

namespace Function

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

/-- The occurrence count as a sum of indicators over the positions. -/
theorem occCount_eq_sum [Fintype X] [DecidableEq S] (w : X → S) (a : S) :
    occCount w a = ∑ i : X, if w i = a then 1 else 0 := by
  rw [occCount_eq_card_filter, card_filter]

/-- Multiplicity grows along an embedding preserving the observed values. -/
theorem occCount_le_of_comp {Y : Type*} {u : X → S} {v : Y → S}
    (e : X ↪ Y) (he : ∀ i, v (e i) = u i) (a : S) [Finite {y // v y = a}] :
    occCount u a ≤ occCount v a := by
  let f : {x // u x = a} ↪ {y // v y = a} :=
    e.subtypeMap (fun {x} hx => (he x).trans hx)
  exact Nat.card_le_card_of_injective f f.injective

/-- An embedding that misses an occurrence gives strictly smaller multiplicity. -/
theorem occCount_lt_of_comp {Y : Type*} {u : X → S} {v : Y → S} {a : S}
    [Finite {y // v y = a}] {j : Y} (e : X ↪ Y) (he : ∀ i, v (e i) = u i)
    (hj : v j = a) (hmiss : ∀ i, e i ≠ j) : occCount u a < occCount v a := by
  let f : {x // u x = a} ↪ {y // v y = a} :=
    e.subtypeMap (fun {x} hx => (he x).trans hx)
  have : Finite {x // u x = a} := Finite.of_injective f f.injective
  let _ := Fintype.ofFinite {x // u x = a}
  let _ := Fintype.ofFinite {y // v y = a}
  rw [occCount_def, occCount_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective f f.injective
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ⟨j, hj⟩
  exact hmiss x (congrArg Subtype.val hx)

/-- Positive multiplicity means the value occurs. -/
@[simp, grind =]
theorem occCount_pos (obs : X → S) (σ : S) [Finite {x // obs x = σ}] :
    0 < occCount obs σ ↔ ∃ x, obs x = σ := by
  simp only [occCount_def, Nat.card_pos_iff, nonempty_subtype,
    and_iff_left (inferInstance : Finite {x // obs x = σ})]

open scoped Classical in
/-- An injective observation map gives multiplicity one precisely on its range. -/
@[simp]
theorem occCount_of_injective (obs : X → S) (hinj : Function.Injective obs) (σ : S) :
    occCount obs σ = if ∃ x, obs x = σ then 1 else 0 := by
  rw [occCount_def]
  split_ifs with h
  · have hc := Nat.card_preimage_of_injective hinj (Set.singleton_subset_iff.mpr h)
    simpa only [Set.preimage, Set.mem_singleton_iff, Set.coe_ofPred, Nat.card_unique] using hc
  · have he := Set.preimage_singleton_eq_empty.mpr h
    simpa [Set.preimage, Set.coe_ofPred] using congrArg (fun s : Set X => Nat.card s) he

/-- Multiplicity-weighted sums over a finite set containing the observed range equal sums over
all indices. -/
theorem sum_occCount_nsmul [Fintype X] {K : Type*} [AddCommMonoid K]
    (obs : X → S) {T : Finset S} (hT : ∀ x, obs x ∈ T) (weight : S → K) :
    ∑ σ ∈ T, occCount obs σ • weight σ = ∑ x, weight (obs x) := by
  classical
  simpa only [Finset.sum_const, occCount_eq_card_filter] using
    Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := T) (g := obs)
      (fun x _ => hT x) weight

/-- Occurrence counts over a finite candidate set containing the observed range sum to the size of
the original family. -/
theorem sum_occCount_eq_card [Finite X] (obs : X → S) {T : Finset S}
    (hT : ∀ x, obs x ∈ T) : ∑ σ ∈ T, occCount obs σ = Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  simpa [Nat.card_eq_fintype_card] using sum_occCount_nsmul obs hT (fun _ => (1 : ℕ))

end Function
