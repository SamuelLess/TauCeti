/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Polynomial
public import Mathlib.Algebra.Polynomial.Roots

/-! # Sign determination at polynomial roots

`tarskiQuery p q` sums the signs of `q` at the distinct roots of `p`.
For nonzero `p`, these are precisely its zeros in the coefficient ring.
For `p = 0`, the query is defined to be zero; it does not describe the infinite zero set.
`tarskiQuery_eq_sum_signCount` is the BKR matrix identity at polynomial roots;
`fullInverse_mulVec_tarskiQuery` recovers the number of distinct roots
realizing each sign condition.
The zero and unit laws reduce queries to zero or a distinct-root count, while
`tarskiQuery_eq_card_sub_card` expresses a query as a difference of sign counts.
The proofs use finite sign determination without Sturm theory.
-/

public section

open SignType Finset TauCeti.SignDetermination
open scoped Matrix

namespace Polynomial

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

theorem tarskiQuery_eq_signSum (p q : R[X]) :
    tarskiQuery p q = signSum p.roots.toFinset q := (rfl)

/-- The Tarski query expressed as a sum over distinct polynomial roots. -/
theorem tarskiQuery_eq_sum (p q : R[X]) :
    tarskiQuery p q = ∑ x ∈ p.roots.toFinset, (sign (q.eval x) : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_eq_sum]

/-- The Tarski query is the positive root count minus the negative root count. -/
theorem tarskiQuery_eq_card_sub_card (p q : R[X]) :
    tarskiQuery p q = ((p.roots.toFinset.filter (fun x => 0 < q.eval x)).card : ℤ) -
      (p.roots.toFinset.filter (fun x => q.eval x < 0)).card := by
  rw [tarskiQuery_eq_signSum, signSum_eq_card_sub_card]

@[simp, grind =]
theorem tarskiQuery_zero_left (q : R[X]) : tarskiQuery 0 q = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_zero_right (p : R[X]) : tarskiQuery p 0 = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_one [ZeroLEOneClass R] (p : R[X]) :
    tarskiQuery p 1 = p.roots.toFinset.card := by
  simp [tarskiQuery_eq_signSum]

/-- A positive count at the roots of a nonzero polynomial is an actual realizable condition. -/
theorem signCount_roots_pos {J : Type*}
    {p : R[X]} (hp : p ≠ 0) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : R, p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp only [signCount_pos, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

end Basic

section Moments

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign-matrix identity for Tarski queries at distinct polynomial roots. -/
theorem tarskiQuery_eq_sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) (e : J → ℕ) :
    tarskiQuery p (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) *
        (signCount p.roots.toFinset Q σ : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_eq_sum_signCount]

/-- Inverting the full matrix of Tarski queries counts distinct roots for each sign condition. -/
theorem fullInverse_mulVec_tarskiQuery {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (tarskiQuery p (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount p.roots.toFinset Q σ : ℚ) := by
  simp only [tarskiQuery_eq_signSum, fullInverse_mulVec_signSum]


end Moments

end Polynomial
