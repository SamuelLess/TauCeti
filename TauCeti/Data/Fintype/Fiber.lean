/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Occurrence counts in finite families

`occCount f y` counts the indices at which a family `f` takes the value `y`.
For an infinite fiber its value is zero, following the convention of `Nat.card`.
Occurrence counts regroup sums over a finite family by fibers: each value in a finite set
covering the range is weighted by its occurrence count.

## Main results

* `Function.occCount_pos`: for a finite fiber, the count is positive exactly when it is nonempty.
* `Function.occCount_of_injective`: an injective function has count one on its range
  and zero outside.
* `Function.occCount_le_of_comp`, `Function.occCount_lt_of_comp`: comparison along embeddings.
* `Function.sum_occCount_nsmul`: regroup a sum by counting the occurrences of each value.
* `Function.sum_occCount_eq_card`: the total occurrence count is the cardinality of the index type.

-/

public section

open Finset

namespace Function

variable {X S : Type*}

/-- The cardinality of a fiber, counting occurrences of a value in a family. -/
noncomputable def occCount (f : X → S) (y : S) : ℕ := Nat.card {x // f x = y}

/-- Occurrence counts are natural cardinalities of fibers. -/
theorem occCount_def (f : X → S) (y : S) :
    occCount f y = Nat.card {x // f x = y} := (rfl)

/-- The occurrence count is the `Finset.card` of the indices taking the given value. -/
theorem occCount_eq_card_filter [Fintype X] [DecidableEq S] (f : X → S) (y : S) :
    occCount f y = (Finset.univ.filter (fun x => f x = y)).card := by
  rw [occCount_def, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The occurrence count as a sum of indicators over the positions. -/
theorem occCount_eq_sum [Fintype X] [DecidableEq S] (w : X → S) (a : S) :
    occCount w a = ∑ i : X, if w i = a then 1 else 0 := by
  rw [occCount_eq_card_filter, card_filter]

/-- Occurrence counts grow along an embedding preserving the values. -/
theorem occCount_le_of_comp {Y : Type*} {u : X → S} {v : Y → S}
    (e : X ↪ Y) (he : ∀ i, v (e i) = u i) (a : S) [Finite {y // v y = a}] :
    occCount u a ≤ occCount v a := by
  let f : {x // u x = a} ↪ {y // v y = a} :=
    e.subtypeMap (fun {x} hx => (he x).trans hx)
  exact Nat.card_le_card_of_injective f f.injective

/-- An embedding that misses an occurrence gives a strictly smaller occurrence count. -/
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

/-- For a finite fiber, positive occurrence count is equivalent to the value being attained. -/
@[simp, grind =]
theorem occCount_pos (f : X → S) (y : S) [Finite {x // f x = y}] :
    0 < occCount f y ↔ ∃ x, f x = y := by
  simp only [occCount_def, Nat.card_pos_iff, nonempty_subtype,
    and_iff_left (inferInstance : Finite {x // f x = y})]

/-- A value outside the range has occurrence count zero. -/
@[simp]
theorem occCount_eq_zero (f : X → S) (y : S) (h : ∀ x, f x ≠ y) :
    occCount f y = 0 := by
  have hnot : y ∉ Set.range f := by simpa only [Set.mem_range, not_exists] using h
  have he := Set.preimage_singleton_eq_empty.mpr hnot
  simpa [occCount_def, Set.preimage, Set.coe_ofPred] using
    congrArg (fun s : Set X => Nat.card s) he

open scoped Classical in
/-- An injective function gives occurrence count one precisely on its range. -/
theorem occCount_of_injective (f : X → S) (hinj : Function.Injective f) (y : S) :
    occCount f y = if ∃ x, f x = y then 1 else 0 := by
  rw [occCount_def]
  split_ifs with h
  · have hc := Nat.card_preimage_of_injective hinj (Set.singleton_subset_iff.mpr h)
    simpa only [Set.preimage, Set.mem_singleton_iff, Set.coe_ofPred, Nat.card_unique] using hc
  · exact occCount_eq_zero f y (not_exists.mp h)

/-- Every value of an injective function occurs exactly once. -/
@[simp]
theorem occCount_eq_one (f : X → S) (hinj : Function.Injective f) (x : X) :
    occCount f (f x) = 1 := by
  rw [occCount_of_injective f hinj, ite_eq_left ⟨x, rfl⟩]

/-- Weighting each value by its occurrence count gives the sum of the weights over all indices. -/
theorem sum_occCount_nsmul [Fintype X] {K : Type*} [AddCommMonoid K]
    (f : X → S) {T : Finset S} (hT : ∀ x, f x ∈ T) (weight : S → K) :
    ∑ y ∈ T, occCount f y • weight y = ∑ x, weight (f x) := by
  classical
  simpa only [Finset.sum_const, occCount_eq_card_filter] using
    Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := T) (g := f)
      (fun x _ => hT x) weight

/-- Occurrence counts over a finite set containing the range sum to the size of
the original family. -/
theorem sum_occCount_eq_card [Finite X] (f : X → S) {T : Finset S}
    (hT : ∀ x, f x ∈ T) : ∑ y ∈ T, occCount f y = Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  simpa [Nat.card_eq_fintype_card] using sum_occCount_nsmul f hT (fun _ => (1 : ℕ))

end Function
