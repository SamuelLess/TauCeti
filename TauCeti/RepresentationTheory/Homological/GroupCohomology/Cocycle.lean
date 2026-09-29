/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Identities of unbundled `1`-cocycles

Facts about a `1`-cocycle `f : G → M` in the sense of Mathlib's unbundled
`groupCohomology.IsCocycle₁`, which need no topology and no representation:

* `groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁`: conjugating the argument by `k`
  changes the value, after the action of `k`, by the coboundary of `f k`.
* `groupCohomology.smul_zero_of_isCocycle₁`: an action admitting a `1`-cocycle fixes `0`.
* `groupCohomology.zeroLocus`: the zero locus `{g | f g = 0}` is a subgroup of `G`, for any group
  action (not necessarily distributive) admitting the cocycle.

Continuous cohomology uses the conjugation identity in transgression, and the zero locus to show
that a continuous `1`-cocycle is determined by its values on a topological generating set.
-/

public section

namespace groupCohomology

/-- Conjugating the argument of a `1`-cocycle by `k` changes its value, after the action of `k`,
by the coboundary of `c k`. Only the cocycle identity is used, so a bare scalar action suffices. -/
theorem smul_apply_inv_mul_mul_of_isCocycle₁ {G M : Type*} [Group G] [AddCommGroup M] [SMul G M]
    {c : G → M} (hc : IsCocycle₁ c) (k m : G) :
    k • c (k⁻¹ * m * k) = m • c k - c k + c m := by
  have hmul : k * (k⁻¹ * m * k) = m * k := by group
  have h := hc k (k⁻¹ * m * k)
  rw [hmul, hc m k] at h
  rw [eq_sub_of_add_eq h.symm]
  abel

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M]

/-- An action admitting a `1`-cocycle fixes `0`: `f g = f (g * 1) = g • f 1 + f g` and `f 1 = 0`.
So a cocycle needs no distributive action for `g • 0 = 0`. -/
theorem smul_zero_of_isCocycle₁ {f : G → M} (hf : IsCocycle₁ f) (g : G) : g • (0 : M) = 0 := by
  simpa only [mul_one, map_one_of_isCocycle₁ hf, right_eq_add] using hf g 1

/-- **The zero locus of a `1`-cocycle is a subgroup.** The cocycle identity
`f (g * h) = g • f h + f g` closes it under multiplication, and the inverse formula
`g • f g⁻¹ = -f g` closes it under inversion. Both steps use `g • 0 = 0`, which the cocycle itself
provides (`smul_zero_of_isCocycle₁`), so the action need not be distributive. -/
def zeroLocus {f : G → M} (hf : IsCocycle₁ f) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := map_one_of_isCocycle₁ hf
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [hf g h, hg, hh, smul_zero_of_isCocycle₁ hf, add_zero]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := map_inv_of_isCocycle₁ hf g
    rwa [hg, neg_zero, ← smul_zero_of_isCocycle₁ hf g, smul_left_cancel_iff] at h

/-- An element lies in the zero locus of a `1`-cocycle exactly when the cocycle vanishes there. -/
@[simp]
theorem mem_zeroLocus {f : G → M} (hf : IsCocycle₁ f) {g : G} : g ∈ zeroLocus hf ↔ f g = 0 :=
  Iff.rfl

end groupCohomology
