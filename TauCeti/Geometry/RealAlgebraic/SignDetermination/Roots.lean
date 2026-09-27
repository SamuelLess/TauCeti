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
The moment identities here specialize finite sign determination without using Sturm theory.
-/

public section

open Polynomial SignType
open scoped Matrix

namespace TauCeti.SignDetermination

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

theorem tarskiQuery_eq_signSum (p q : R[X]) :
    tarskiQuery p q = signSum p.roots.toFinset q := (rfl)

/-- The sign-matrix identity for Tarski queries at distinct polynomial roots. -/
theorem tarskiQuery_prod_pow {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) (e : J → ℕ) :
    tarskiQuery p (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) *
        (signCount p.roots.toFinset Q σ : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_prod_pow]

/-- Inverting the full matrix of Tarski queries recovers the root sign multiplicities. -/
theorem fullInverse_mulVec_tarskiQuery {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (tarskiQuery p (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount p.roots.toFinset Q σ : ℚ) := by
  simp only [tarskiQuery_eq_signSum, fullInverse_mulVec_signSum]

/-- A positive count at the roots of a nonzero polynomial is an actual realizable condition. -/
theorem signCount_roots_pos {J : Type*} [Fintype J]
    {p : R[X]} (hp : p ≠ 0) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : R, p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp only [signCount_eq_fiberCount, fiberCount_pos, funext_iff, Subtype.exists,
    Multiset.mem_toFinset, mem_roots hp, IsRoot.def, exists_prop]

end TauCeti.SignDetermination
