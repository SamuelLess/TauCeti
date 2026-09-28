/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Abel

/-! # Summing finitely many jumps on an ordered interval

A function into an additive commutative group, constant between finitely many events, has total
change equal to the sum of its local changes. This is the finite telescoping
step in the signed Sturm theorem; it uses no topology or completeness.
-/

public section

namespace Finset

open Set

variable {R : Type*} [LinearOrder R] [DenselyOrdered R]

/-- Choose a point to the right of an event, before all later events and a given bound. -/
theorem exists_right_gap (S : Finset R) {r b : R} (hrb : r < b) :
    ∃ c, r < c ∧ c < b ∧ ∀ x ∈ S, r < x → c < x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨c, hrc, hcb⟩ := exists_between hrb
    exact ⟨c, hrc, hcb, by simp⟩
  | @insert x S _ ih =>
    obtain ⟨c, hrc, hcb, hc⟩ := ih
    by_cases hrx : r < x
    · obtain ⟨d, hrd, hdc⟩ := exists_between (lt_min hrc hrx)
      refine ⟨d, hrd, (hdc.trans_le (min_le_left _ _)).trans hcb, ?_⟩
      intro y hy hry
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hdc.trans_le (min_le_right _ _)
      · exact (hdc.trans_le (min_le_left _ _)).trans (hc y hy hry)
    · exact ⟨c, hrc, hcb, fun y hy hry => by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hrx hry).elim
        · exact hc y hy hry⟩

/-- Choose a point to the left of an event, after all earlier events and a given bound. -/
theorem exists_left_gap (S : Finset R) {a r : R} (har : a < r) :
    ∃ c, a < c ∧ c < r ∧ ∀ x ∈ S, x < r → x < c := by
  obtain ⟨c, hcr, hac, hc⟩ := exists_right_gap (R := OrderDual R) S (r := r) (b := a) har
  exact ⟨c, hac, hcr, hc⟩

/-- Local changes at isolated events sum to the total change between two
points outside the event set. -/
theorem sum_jumps {G : Type*} [AddCommGroup G] (S : Finset R) (V w : R → G)
    (hconst : ∀ a b, a < b → (∀ x ∈ S, x ∉ Icc a b) → V a = V b)
    (hjump : ∀ a r b, a < r → r < b → r ∈ S →
      (∀ x ∈ S, x ∈ Icc a b → x = r) → V a - V b = w r)
    {a b : R} (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) :
    V a - V b = ∑ x ∈ S.filter (fun x => a < x ∧ x < b), w x := by
  classical
  induction hn : (S.filter (fun x => a < x ∧ x < b)).card using Nat.strong_induction_on
      generalizing a b with
  | h n ih =>
    let T := S.filter (fun x => a < x ∧ x < b)
    by_cases hT : T.Nonempty
    · let r := T.min' hT
      have hrT : r ∈ T := Finset.min'_mem T hT
      obtain ⟨hrS, har, hrb⟩ := Finset.mem_filter.mp hrT
      obtain ⟨c, hrc, hcb, hc⟩ := exists_right_gap S hrb
      have hcS : c ∉ S := fun hcS => (hc c hcS hrc).false
      have hsingle : ∀ x ∈ S, x ∈ Icc a c → x = r := by
        intro x hx haxc
        have hax : a < x := haxc.1.lt_of_ne (by rintro rfl; exact ha hx)
        have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hax, haxc.2.trans_lt hcb⟩
        have hrx : r ≤ x := Finset.min'_le T x hxT
        by_contra hne
        have hrcx := hc x hx (hrx.lt_of_ne (Ne.symm hne))
        exact hrcx.not_ge haxc.2
      let U := S.filter (fun x => c < x ∧ x < b)
      have hrU : r ∉ U := by
        simp only [U, Finset.mem_filter]
        rintro ⟨_, hcr, _⟩
        exact hcr.not_gt hrc
      have hTU : T = insert r U := by
        ext x
        constructor
        · intro hx
          obtain ⟨hxS, hax, hxb⟩ := Finset.mem_filter.mp hx
          by_cases hxr : x = r
          · exact Finset.mem_insert.mpr (Or.inl hxr)
          · apply Finset.mem_insert.mpr
            right
            refine Finset.mem_filter.mpr ⟨hxS, ?_, hxb⟩
            by_contra! hxc
            exact hxr (hsingle x hxS ⟨hax.le, hxc⟩)
        · intro hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hrT
          · obtain ⟨hxS, hcx, hxb⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_filter.mpr ⟨hxS, har.trans (hrc.trans hcx), hxb⟩
      have hcard : U.card < n := by
        have heq : T.card = U.card + 1 := by rw [hTU, Finset.card_insert_of_notMem hrU]
        -- Fold the locally defined filtered set to compare its cardinality with U.
        change T.card = n at hn
        omega
      have hlocal := hjump a r c har hrc hrS hsingle
      have hrest := ih U.card hcard hcb hcS hb rfl
      -- Fold the local filter abbreviation so its partition or emptiness rewrites the sum.
      change V a - V b = ∑ x ∈ T, w x
      rw [hTU, Finset.sum_insert hrU]
      -- The induction hypothesis uses the filter defining U; fold that abbreviation.
      change V c - V b = ∑ x ∈ U, w x at hrest
      calc
        V a - V b = (V a - V c) + (V c - V b) := by abel
        _ = w r + ∑ x ∈ U, w x := by rw [hlocal, hrest]
    · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      have hno : ∀ x ∈ S, x ∉ Icc a b := by
        intro x hx hxab
        have hax : a < x := hxab.1.lt_of_ne (by rintro rfl; exact ha hx)
        have hxb : x < b := hxab.2.lt_of_ne (by rintro rfl; exact hb hx)
        have : x ∈ T := Finset.mem_filter.mpr ⟨hx, hax, hxb⟩
        simp [hT0] at this
      -- Fold the local filter abbreviation so its partition or emptiness rewrites the sum.
      change V a - V b = ∑ x ∈ T, w x
      simp [hT0, hconst a b hab hno]

end Finset
