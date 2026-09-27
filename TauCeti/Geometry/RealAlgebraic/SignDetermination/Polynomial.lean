/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Moments
public import Mathlib.Algebra.Polynomial.Roots

/-! # Sign determination from polynomial sign sums

This file concerns mathematical finite sums over any ordered field.
Taking the finite set to be the distinct roots of a nonzero polynomial gives
the sign-determination moment identity. No real-closed-field hypothesis is
needed for this finite algebraic identity.
-/

public section

open Polynomial SignType
open scoped BigOperators Matrix

namespace SignDetermination

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Polynomial evaluation followed by sign and the rational sign-code cast. -/
@[expose] noncomputable def signEval (x : R) : R[X] →*₀ ℚ :=
  SignType.castHom.comp (signHom.comp (Polynomial.evalRingHom x).toMonoidWithZeroHom)

@[simp] theorem signEval_apply (x : R) (p : R[X]) :
    signEval x p = (sign (p.eval x) : ℚ) := rfl

/-- The mathematical sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℚ := ∑ x : Z, signEval x.val p

/-- Polynomial product sign sums are the moments of the observed sign words. -/
theorem signSum_product {J : Type*} [Fintype J]
    (Z : Finset R) (Q : J → R[X]) (e : J → ℕ) :
    signSum Z (∏ j, Q j ^ e j) =
      ∑ x : Z, ∏ j, ((sign ((Q j).eval x.val) : SignType) : ℚ) ^ e j := by
  simp only [signSum, map_prod, map_pow, signEval_apply]

/-- The polynomial moment identity on any complete restricted column set and
any selected exponent rows. Exponents need not be bounded by two. -/
theorem restricted_moments {J C I : Type*} [Fintype J]
    [Fintype C] (Z : Finset R) (Q : J → R[X])
    (columns : C → (J → SignType)) (rows : I → J → ℕ)
    (hinj : Function.Injective columns)
    (cover : ∀ x : Z, ∃ c, columns c = fun j => sign ((Q j).eval x.val)) :
    (Matrix.of fun i c => ∏ j, (columns c j : ℚ) ^ rows i j) *ᵥ
        (fun c => count (fun x : Z => fun j => sign ((Q j).eval x.val)) (columns c)) =
      fun i => signSum Z (∏ j, Q j ^ rows i j) := by
  classical
  simp_rw [signSum_product]
  exact count_moments _ columns hinj cover (fun i σ => ∏ j, (σ j : ℚ) ^ rows i j)

/-- All ternary moments determine the exact multiplicity of every sign pattern.
Taking `Z` to be the distinct roots in an interval gives the abstract BKR
sign-determination identity, without any root-separation hypothesis. -/
theorem recover_signs {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => signSum Z (∏ j, Q j ^ (e j).val)) =
      fun σ => count (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := by
  simp_rw [signSum_product]
  exact full_recovery J _

/-- The integer BKR moment identity on the distinct roots of a polynomial.
For nonzero `p` these are precisely its zeros. As a finite-list identity it also
holds for `p = 0`, whose `roots` multiset is empty. -/
theorem sign_matrix (p : R[X]) {J : Type*} [Fintype J] [DecidableEq J]
    (Q : J → R[X]) (e : J → ℕ) :
    (∑ x ∈ p.roots.toFinset, (sign ((∏ j, Q j ^ e j).eval x) : ℤ)) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) *
        ((p.roots.toFinset.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card : ℤ) := by
  classical
  let Z := p.roots.toFinset
  let obs (x : Z) (j : J) := sign ((Q j).eval x.val)
  have h := congrFun (count_moments_int obs id Function.injective_id
    (fun x => ⟨obs x, rfl⟩) (fun (_ : Unit) σ => ∏ j, (σ j : ℤ) ^ e j)) ()
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, id_eq] at h
  have counts (σ : J → SignType) :
      (Finset.univ.filter fun x : Z => obs x = σ).card =
        (Z.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card := by
    simp only [obs, funext_iff]
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨x.property, hx⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
    · intro x hx
      exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
        by simpa using (Finset.mem_filter.mp hx).2, rfl⟩
  simp_rw [counts] at h
  rw [h]
  rw [Finset.sum_subtype Z (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro x _
  change (SignType.castHom.comp (signHom.comp (Polynomial.evalRingHom x.val).toMonoidWithZeroHom)
    (∏ j, Q j ^ e j) : ℤ) = _
  simp [map_prod, map_pow, obs]

/-- The recovered sign pattern occurs at exactly as many points as its count. -/
theorem recovered_pos {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < (fullInverse J *ᵥ (fun e => signSum Z (∏ j, Q j ^ (e j).val))) σ ↔
      ∃ x : Z, ∀ j, sign ((Q j).eval x.val) = σ j := by
  rw [recover_signs, count_pos]
  simp only [funext_iff]

end SignDetermination
