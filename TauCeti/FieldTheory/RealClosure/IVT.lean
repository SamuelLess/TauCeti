/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
import Mathlib.FieldTheory.Minpoly.Finite
import TauCeti.Algebra.Polynomial.LinearFactor
import TauCeti.Algebra.Polynomial.RealClosed.Quadratic

/-! # Polynomial intermediate values over an abstract real closed field

The polynomial API gives roots from strict or weak endpoint sign changes and both
orientations of closed-interval image inclusion. `Polynomial.eval_mul_pos_of_no_roots`
is the constant-sign result used by polynomial Rolle.

Irreducible factors have degree at most two; quadratic factors have constant
nonzero sign, so a sign change forces a root of a linear factor.

The degree bound generalizes Mathlib's `Irreducible.natDegree_le_two` from
`Mathlib.Analysis.Complex.Polynomial.Basic`, following its root, minimal polynomial,
and finite-dimension proof over an arbitrary real closed field.

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
theorem _root_.Polynomial.natDegree_le_two_of_irreducible {p : R[X]} (hp : Irreducible p) :
    p.natDegree ≤ 2 := by
  have := isAlgClosed_quadraticAlgebra (R := R)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero
    (QuadraticAlgebra R (-1) 0) p (degree_pos_of_irreducible hp).ne'
  have heq := minpoly.eq_of_irreducible hp hz
  have hdeg : p.natDegree = (minpoly R z).natDegree := by
    rw [← heq, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero))]
  rw [hdeg]
  exact (minpoly.natDegree_le z).trans_eq (QuadraticAlgebra.finrank_eq_two _ _)

/-- A polynomial has constant nonzero sign on any closed interval containing
none of its roots. -/
theorem _root_.Polynomial.eval_mul_pos_of_no_roots (p : R[X]) {a b : R} (hab : a ≤ b)
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
      (fun h => linear_eval_mul_pos_of_no_roots h hab hq')
      (fun h => irreducible_quadratic_eval_mul_pos hq h a b)
    simpa only [eval_mul, mul_mul_mul_comm] using mul_pos hqpos (ih hp')

/-- A nonpositive product of endpoint values gives a root on the closed interval. -/
theorem _root_.Polynomial.exists_root_Icc_of_mul_nonpos (p : R[X]) {a b : R} (hab : a ≤ b)
    (h : p.eval a * p.eval b ≤ 0) : ∃ c ∈ Set.Icc a b, p.eval c = 0 := by
  by_contra! hroot
  exact not_le_of_gt (eval_mul_pos_of_no_roots p hab hroot) h

/-- Weakly opposite endpoint signs give a root on the closed interval. -/
theorem _root_.Polynomial.exists_root_Icc (p : R[X]) {a b : R} (hab : a ≤ b)
    (ha : p.eval a ≤ 0) (hb : 0 ≤ p.eval b) :
    ∃ c ∈ Set.Icc a b, p.eval c = 0 :=
  exists_root_Icc_of_mul_nonpos p hab (mul_nonpos_of_nonpos_of_nonneg ha hb)

/-- Polynomial IVT over an arbitrary real closed ordered field, including
non-Archimedean fields. -/
theorem _root_.Polynomial.exists_root_Ioo (p : R[X]) {a b : R} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  obtain ⟨c, ⟨hac, hcb⟩, hc⟩ := exists_root_Icc p hab.le ha.le hb.le
  refine ⟨c, ⟨hac.lt_of_ne ?_, hcb.lt_of_ne ?_⟩, hc⟩
  · rintro rfl
    exact ha.ne hc
  · rintro rfl
    exact hb.ne' hc

/-- The symmetric sign-change form of polynomial IVT. -/
theorem _root_.Polynomial.exists_root_Ioo_of_mul_neg (p : R[X]) {a b : R} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ c ∈ Set.Ioo a b, p.eval c = 0 := by
  rcases mul_neg_iff.mp h with h | h
  · obtain ⟨c, hc, he⟩ := exists_root_Ioo (-p) hab (by simpa using h.1) (by simpa using h.2)
    exact ⟨c, hc, by simpa using he⟩
  · exact exists_root_Ioo p hab h.1 h.2

/-- Polynomial intermediate value on a closed interval, for `p.eval a ≤ y ≤ p.eval b`. -/
theorem _root_.Polynomial.intermediate_value_Icc (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval a) (p.eval b) ⊆ p.eval '' Set.Icc a b := by
  rintro y ⟨hay, hyb⟩
  obtain ⟨c, hc, he⟩ := exists_root_Icc (p - C y) hab
    (by simpa using sub_nonpos.mpr hay) (by simpa using sub_nonneg.mpr hyb)
  exact ⟨c, hc, by simpa only [eval_sub, eval_C, sub_eq_zero] using he⟩

/-- Polynomial intermediate value on a closed interval, for `p.eval b ≤ y ≤ p.eval a`. -/
theorem _root_.Polynomial.intermediate_value_Icc' (p : R[X]) {a b : R} (hab : a ≤ b) :
    Set.Icc (p.eval b) (p.eval a) ⊆ p.eval '' Set.Icc a b := by
  rintro y ⟨hby, hya⟩
  obtain ⟨c, hc, he⟩ := exists_root_Icc (C y - p) hab
    (by simpa using sub_nonpos.mpr hya) (by simpa using sub_nonneg.mpr hby)
  exact ⟨c, hc, (by simpa only [eval_sub, eval_C, sub_eq_zero] using he : y = p.eval c).symm⟩

end TauCeti.RealClosure
