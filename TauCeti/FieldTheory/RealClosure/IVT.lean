/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Polynomial.LinearFactor
import TauCeti.Algebra.Polynomial.RealClosed.Quadratic
import Mathlib.Tactic.Ring

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

omit [IsRealClosed R] in
/-- A linear polynomial has constant nonzero sign on an interval without a root. -/
theorem linear_eval_mul_pos {p : R[X]} (hdeg : p.natDegree = 1) {a b : R}
    (hab : a ≤ b) (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    0 < p.eval a * p.eval b := by
  have hd : p.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr hdeg
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hd
  obtain ⟨c, hc⟩ := exists_eq_C_mul_X_sub_C_of_natDegree_le_one hdeg.le hr
  have hcne : c ≠ 0 := by
    intro hz
    apply hroot a ⟨le_rfl, hab⟩
    simp [hc, hz]
  have hprod : 0 < (a - r) * (b - r) := by
    rcases lt_or_ge r a with h | h
    · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans_le hab))
    · have hb : b < r := by
        by_contra! hb
        exact hroot r ⟨h, hb⟩ hr
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans_lt hb)) (sub_neg.mpr hb)
  simp only [hc, eval_mul, eval_C, eval_sub, eval_X]
  convert mul_pos (mul_self_pos.mpr hcne) hprod using 1
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

/-- Weakly opposite endpoint signs give a root on the closed interval. -/
theorem exists_root_Icc (p : R[X]) {a b : R} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b) :
    ∃ c ∈ Set.Icc a b, p.eval c = 0 := by
  by_contra! h
  exact not_le_of_gt (eval_mul_pos_of_no_roots p hab h)
    (mul_nonpos_of_nonpos_of_nonneg ha hb)

/-- Polynomial IVT over an arbitrary real closed ordered field, including
non-Archimedean fields. -/
theorem ivt (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ := exists_root_Icc p hab.le ha.le hb.le
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
  obtain ⟨c, hc, he⟩ := exists_root_Icc (p - C y) hab
    (by simpa using sub_nonpos.mpr hay) (by simpa using sub_nonneg.mpr hyb)
  exact ⟨c, hc, by simpa only [eval_sub, eval_C, sub_eq_zero] using he⟩

/-- Every value between the endpoint values in reversed order is attained. -/
theorem _root_.Polynomial.intermediate_value_Icc' (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval b) (p.eval a) ⊆ p.eval '' Set.Icc a b := by
  rintro y ⟨hby, hya⟩
  obtain ⟨c, hc, he⟩ := exists_root_Icc (C y - p) hab
    (by simpa using sub_nonpos.mpr hya) (by simpa using sub_nonneg.mpr hby)
  exact ⟨c, hc, (by simpa only [eval_sub, eval_C, sub_eq_zero] using he : y = p.eval c).symm⟩

end TauCeti.RealClosure
