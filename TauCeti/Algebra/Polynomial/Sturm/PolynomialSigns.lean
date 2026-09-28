/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
public import Mathlib.Basic.Sign.Basic
import TauCeti.Algebra.Polynomial.LinearFactor
import TauCeti.Algebra.Polynomial.RealClosed.Quadratic

/-! # Polynomial signs at infinity over a real closed field

The bounds here are elements of the field, and need not be Archimedean-finite.
The proof uses factorization into linear and irreducible quadratic factors.
-/

public section

namespace Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- Beyond some field-valued bound, a polynomial has the sign of its leading coefficient. -/
theorem sign_at_top (p : R[X]) : ∃ B : R, ∀ x, B < x →
    SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact ⟨0, by simp⟩
  | unit p hp =>
    refine ⟨0, fun x _ => ?_⟩
    have heq := eq_C_of_degree_eq_zero (isUnit_iff_degree_eq_zero.mp hp)
    rw [heq]
    simp
  | mul p q _ hq ih =>
    obtain ⟨B, hB⟩ := ih
    have hdeg : q.natDegree = 1 ∨ q.natDegree = 2 := by
      have := q.natDegree_le_two_of_irreducible hq
      have := hq.natDegree_pos
      omega
    have hqsign : ∃ C : R, ∀ x, C < x →
        SignType.sign (q.eval x) = SignType.sign q.leadingCoeff := by
      rcases hdeg with hdeg | hdeg
      · have hd : q.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr hdeg
        obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hd
        refine ⟨r, fun x hx => ?_⟩
        obtain ⟨c, hc⟩ := exists_eq_C_mul_X_sub_C_of_natDegree_le_one hdeg.le hr
        simp only [hc, eval_mul, eval_C, eval_sub, eval_X, leadingCoeff_mul,
          leadingCoeff_C, leadingCoeff_X_sub_C, mul_one, sign_mul,
          sign_pos (sub_pos.mpr hx)]
      · refine ⟨0, fun x _ => ?_⟩
        rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hq.ne_zero) with h | h
        · rw [sign_neg h, sign_neg
            ((TauCeti.irreducible_quadratic_eval_neg_iff_leadingCoeff_neg hq hdeg x).mpr h)]
        · rw [sign_pos h, sign_pos
            ((TauCeti.irreducible_quadratic_eval_pos_iff_leadingCoeff_pos hq hdeg x).mpr h)]
    obtain ⟨C, hC⟩ := hqsign
    refine ⟨max B C, fun x hx => ?_⟩
    rw [eval_mul, leadingCoeff_mul, sign_mul, sign_mul,
      hB x ((le_max_left _ _).trans_lt hx), hC x ((le_max_right _ _).trans_lt hx)]

/-- Below some field-valued bound, the sign gains the degree-parity factor. -/
theorem sign_at_bot (p : R[X]) : ∃ B : R, ∀ x, x < B →
    SignType.sign (p.eval x) = SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  obtain ⟨B, hB⟩ := sign_at_top (p.comp (-X))
  refine ⟨-B, fun x hx => ?_⟩
  have hs := hB (-x) (by linarith)
  simpa only [eval_comp, eval_neg, eval_X, neg_neg,
    leadingCoeff_comp (by simp : (-X : R[X]).natDegree ≠ 0),
    leadingCoeff_neg, leadingCoeff_X] using hs

end Polynomial
