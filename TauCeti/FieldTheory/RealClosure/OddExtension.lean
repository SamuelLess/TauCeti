/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.PolynomialCone
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Extending an ordering across odd-degree algebraic adjunctions

An ordering extends across an irreducible odd-degree adjunction (`AdjoinRoot.exists_linearOrder`).
Every odd-degree polynomial has an irreducible factor of odd degree.

The proof descends in odd degree. A putative negative weighted-square
certificate lifts to an even-degree polynomial; division by the defining
odd-degree polynomial produces a smaller odd-degree obstruction.

## References

The odd-degree descent is the classical Artin–Schreier argument; see Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 4](https://www.math.uni-konstanz.de/algebra/WS0910/Notes04.pdf),
§3.
-/

public section

namespace Polynomial

variable {K : Type*} [CommSemiring K] [NoZeroDivisors K] [WfDvdMonoid K]

/-- An odd-degree polynomial has an odd-degree irreducible factor. -/
theorem exists_irreducible_factor_of_odd_natDegree (p : K[X]) (hp : Odd p.natDegree) :
    ∃ q : K[X], Irreducible q ∧ Odd q.natDegree ∧ q ∣ p := by
  revert hp
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit p hp => simp [natDegree_eq_zero_of_isUnit hp]
  | mul p q hp hq ih =>
    intro hodd
    by_cases hoddq : Odd q.natDegree
    · exact ⟨q, hq, hoddq, dvd_mul_right q p⟩
    have hoddp : Odd p.natDegree := by
      rw [natDegree_mul hq.ne_zero hp, Nat.odd_iff] at hodd
      rw [Nat.odd_iff] at hoddq ⊢
      omega
    obtain ⟨r, hr, hrodd, hrp⟩ := ih hoddp
    exact ⟨r, hr, hrodd, hrp.trans (dvd_mul_left p q)⟩

end Polynomial

namespace TauCeti.RealClosure

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A negative weighted-square certificate in an odd-degree adjunction descends
 to an irreducible odd-degree adjunction of smaller degree. -/
private theorem extensionCone.exists_lt (p : K[X]) (hp : Irreducible p)
    (hodd : Odd p.natDegree) (hneg : -1 ∈ extensionCone (algebraMap K (AdjoinRoot p))) :
    ∃ r : K[X], Irreducible r ∧ Odd r.natDegree ∧ r.natDegree < p.natDegree ∧
      -1 ∈ extensionCone (algebraMap K (AdjoinRoot r)) := by
  have : Fact (Irreducible p) := ⟨hp⟩
  obtain ⟨s, hs, hsdeg, hseval⟩ := extensionCone.exists_aeval_root_eq p hp.natDegree_pos hneg
  let w := (1 : K[X]) + s
  have hw : w ∈ extensionCone (C : K →+* K[X]) := add_mem (one_mem _) hs
  have hw0 : w ≠ 0 := by
    intro hz
    have hpos : 0 < w.eval 0 := by
      dsimp [w]
      simp only [eval_add, eval_one]
      linarith [extensionCone.eval_nonneg hs 0]
    simp [hz] at hpos
  have hwdeg : w.natDegree < 2 * p.natDegree := by
    simpa only [w, natDegree_one_add] using hsdeg
  have hweval : aeval (AdjoinRoot.root p) w = 0 := by
    simp only [w, map_add, map_one, hseval, add_neg_cancel]
  have hpw : p ∣ w := AdjoinRoot.mk_eq_zero.mp (by rwa [← AdjoinRoot.aeval_eq])
  obtain ⟨q, hq⟩ := hpw
  have hq0 : q ≠ 0 := by intro hz; apply hw0; simp [hq, hz]
  have hdegrees : w.natDegree = p.natDegree + q.natDegree := by
    rw [hq, natDegree_mul hp.ne_zero hq0]
  have hqdeg : q.natDegree < p.natDegree := by omega
  have hqodd : Odd q.natDegree := by
    have heven := (extensionCone.even_natDegree hw)
    rw [Nat.even_iff, hdegrees] at heven
    rw [Nat.odd_iff] at hodd ⊢
    omega
  obtain ⟨r, hr, hrodd, hrq⟩ := exists_irreducible_factor_of_odd_natDegree q hqodd
  have hrdeg : r.natDegree < p.natDegree :=
    (natDegree_le_of_dvd hrq hq0).trans_lt hqdeg
  have hrw : r ∣ w := by rw [hq]; exact hrq.trans (dvd_mul_left q p)
  have hwr : aeval (AdjoinRoot.root r) w = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.mpr hrw
  have hsr : aeval (AdjoinRoot.root r) s = -1 := by
    have hsum : 1 + aeval (AdjoinRoot.root r) s = 0 := by
      simpa only [w, map_add, map_one] using hwr
    exact eq_neg_of_add_eq_zero_right hsum
  exact ⟨r, hr, hrodd, hrdeg, hsr ▸ extensionCone.aeval_mem hs (AdjoinRoot.root r)⟩

/-- The cone of weighted squares stays proper after adjoining a root of an
irreducible polynomial of odd degree. -/
theorem extensionCone.neg_one_notMem_adjoinRoot (p : K[X]) (hp : Irreducible p)
    (hodd : Odd p.natDegree) :
    -1 ∉ extensionCone (algebraMap K (AdjoinRoot p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hneg
    obtain ⟨r, hr, hrodd, hrdeg, hrneg⟩ := extensionCone.exists_lt p hp hodd hneg
    exact ih r.natDegree (hrdeg.trans_le hn.le) r hr hrodd rfl hrneg

/-- An odd-degree simple field extension admits an order preserving the
given order of the base field. -/
theorem _root_.AdjoinRoot.exists_linearOrder (p : K[X]) [hp : Fact (Irreducible p)]
    (hodd : Odd p.natDegree) :
    ∃ o : LinearOrder (AdjoinRoot p), letI := o
      IsStrictOrderedRing (AdjoinRoot p) ∧ StrictMono (algebraMap K (AdjoinRoot p)) :=
  extensionCone.exists_linearOrder _ (extensionCone.neg_one_notMem_adjoinRoot p hp.out hodd)

end TauCeti.RealClosure
