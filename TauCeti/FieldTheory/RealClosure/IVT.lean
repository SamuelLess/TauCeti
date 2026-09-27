/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

/-! # Polynomial intermediate values over an abstract real closed field
Irreducible factors have degree at most two; quadratic factors have constant
nonzero sign, so a sign change forces a root of a linear factor.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 5](https://www.math.uni-konstanz.de/algebra/WS0910/Notes05.pdf),
Corollaries 3.1 and 3.2.
-/

public section

namespace TauCeti.RealClosure

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Irreducible polynomials over a real closed field have degree at most two. -/
theorem natDegree_le_two_of_irreducible {p : R[X]} (hp : Irreducible p) : p.natDegree ≤ 2 := by
  have := complex_isAlgClosed (R := R)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero
    (QuadraticAlgebra R (-1) 0) p (degree_pos_of_irreducible hp).ne'
  have heq := minpoly.eq_of_irreducible hp hz
  have hdeg : p.natDegree = (minpoly R z).natDegree := by
    rw [← heq, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  rw [hdeg]
  exact (minpoly.natDegree_le z).trans_eq (QuadraticAlgebra.finrank_eq_two _ _)

omit [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A linear polynomial is its leading coefficient times the distance from its root. -/
theorem _root_.Polynomial.eval_eq_leadingCoeff_mul_sub {p : R[X]}
    (hp : p.natDegree = 1) {r : R} (hr : p.IsRoot r) (x : R) :
    p.eval x = p.leadingCoeff * (x - r) := by
  have heq := eq_X_add_C_of_natDegree_le_one hp.le
  have hr' := hr
  rw [IsRoot, heq] at hr'
  simp only [eval_add, eval_mul, eval_C, eval_X] at hr'
  simp only [leadingCoeff, hp]
  conv_lhs => rw [heq]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  linear_combination hr'

/-- An irreducible quadratic has the sign of its leading coefficient everywhere. -/
theorem quadratic_leading_mul_pos {p : R[X]} (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (x : R) : 0 < p.leadingCoeff * p.eval x := by
  have hdisc : discrim (p.coeff 2) (p.coeff 1) (p.coeff 0) < 0 := by
    by_contra! h
    obtain ⟨x, hx⟩ := p.exists_root_of_isSquare_discrim hdeg (IsSquare.of_nonneg h)
    exact hp.not_isRoot_of_natDegree_ne_one (by omega) hx
  have hpos : 0 < (4 * p.coeff 2) * p.eval x := by
    have heval : p.eval x = p.coeff 2 * x ^ 2 + p.coeff 1 * x + p.coeff 0 := by
      conv_lhs => rw [eq_quadratic_of_degree_le_two (natDegree_le_iff_degree_le.mp hdeg.le)]
      simp
    rw [heval]
    dsimp [discrim] at hdisc
    nlinarith [sq_nonneg (2 * p.coeff 2 * x + p.coeff 1)]
  simp only [leadingCoeff, hdeg]
  nlinarith

/-- An irreducible quadratic has the same nonzero sign at any two points. -/
theorem quadratic_eval_mul_pos {p : R[X]} (hp : Irreducible p)
    (hdeg : p.natDegree = 2) (a b : R) : 0 < p.eval a * p.eval b := by
  have hpos := quadratic_leading_mul_pos hp hdeg
  rcases mul_pos_iff.mp (hpos a) with ha | ha <;>
    rcases mul_pos_iff.mp (hpos b) with hb | hb
  · exact mul_pos ha.2 hb.2
  · linarith [ha.1, hb.1]
  · linarith [ha.1, hb.1]
  · exact mul_pos_of_neg_of_neg ha.2 hb.2

omit [IsRealClosed R] in
/-- A linear polynomial has constant nonzero sign on an interval without a root. -/
theorem linear_eval_mul_pos {p : R[X]} (hdeg : p.natDegree = 1) {a b : R}
    (hab : a ≤ b) (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    0 < p.eval a * p.eval b := by
  have hd : p.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr hdeg
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hd
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr
    (ne_zero_of_natDegree_gt (show 0 < p.natDegree by omega))
  have heval := p.eval_eq_leadingCoeff_mul_sub hdeg hr
  have hprod : 0 < (a - r) * (b - r) := by
    rcases lt_or_ge r a with h | h
    · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans_le hab))
    · have hb : b < r := by
        by_contra! hb
        exact hroot r ⟨h, hb⟩ hr
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans_lt hb)) (sub_neg.mpr hb)
  rw [heval a, heval b]
  convert mul_pos (mul_self_pos.mpr hlead) hprod using 1
  ring

/-- A polynomial has constant nonzero sign on any closed interval containing
none of its roots. -/
theorem eval_mul_pos_of_no_roots (p : R[X]) {a b : R} (hab : a ≤ b)
    (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) : 0 < p.eval a * p.eval b := by
  revert hroot
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro hroot
    exact (hroot a ⟨le_rfl, hab⟩ (by simp)).elim
  | unit p hp =>
    intro hroot
    have heq := eq_C_of_degree_eq_zero (isUnit_iff_degree_eq_zero.mp hp)
    have hsame : p.eval b = p.eval a := by rw [heq]; simp
    rw [hsame]
    exact mul_self_pos.mpr (hroot a ⟨le_rfl, hab⟩)
  | mul p q _ hq ih =>
    intro hroot
    have hp' : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0 := by
      intro x hx hp
      apply hroot x hx
      simp [hp]
    have hq' : ∀ x ∈ Set.Icc a b, q.eval x ≠ 0 := by
      intro x hx hq
      apply hroot x hx
      simp [hq]
    have hdeg : q.natDegree = 1 ∨ q.natDegree = 2 := by
      have := natDegree_le_two_of_irreducible hq
      have := hq.natDegree_pos
      omega
    have hqpos : 0 < q.eval a * q.eval b := hdeg.elim
      (fun h => linear_eval_mul_pos h hab hq')
      (fun h => quadratic_eval_mul_pos hq h a b)
    simpa only [eval_mul, mul_mul_mul_comm] using mul_pos hqpos (ih hp')

/-- The endpoint-product theorem also fixes the sign at every point of a root-free interval. -/
theorem eval_mul_pos_on (p : R[X]) {a b : R}
    (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) {x : R} (hx : x ∈ Set.Icc a b) :
    0 < p.eval a * p.eval x :=
  eval_mul_pos_of_no_roots p hx.1 (fun y hy => hroot y ⟨hy.1, hy.2.trans hx.2⟩)

/-- Polynomial IVT over an arbitrary real closed ordered field, including
non-Archimedean fields. -/
theorem ivt (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  have hroot : ∃ c ∈ Set.Icc a b, p.eval c = 0 := by
    by_contra! h
    have hpos := eval_mul_pos_of_no_roots p hab.le h
    exact (mul_neg_of_neg_of_pos ha hb).not_gt hpos
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ := hroot
  refine ⟨c, ⟨hac.lt_of_ne ?_, hcb.lt_of_ne ?_⟩, hc⟩
  · rintro rfl
    exact ha.ne hc
  · rintro rfl
    exact hb.ne' hc

/-- The symmetric sign-change form of polynomial IVT. -/
theorem ivt_of_mul_neg (p : R[X]) {a b : R} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  rcases mul_neg_iff.mp h with h | h
  · obtain ⟨c, hc, he⟩ := ivt (-p) hab (by simpa using h.1) (by simpa using h.2)
    exact ⟨c, hc, by simpa using he⟩
  · exact ivt p hab h.1 h.2

/-- Every value between the endpoint values is attained on the closed interval. -/
theorem _root_.Polynomial.intermediate_value_Icc (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval a) (p.eval b) ⊆ p.eval '' Set.Icc a b := by
  rintro y ⟨hay, hyb⟩
  rcases hay.eq_or_lt with rfl | hay
  · exact ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  rcases hyb.eq_or_lt with rfl | hyb
  · exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  have hab' : a < b := hab.lt_of_ne (by
    rintro rfl
    exact (hay.trans hyb).false)
  obtain ⟨c, hc, he⟩ := ivt (p - C y) hab'
    (by simpa using sub_neg.mpr hay) (by simpa using sub_pos.mpr hyb)
  exact ⟨c, ⟨hc.1.le, hc.2.le⟩, by simpa only [eval_sub, eval_C, sub_eq_zero] using he⟩

end TauCeti.RealClosure
