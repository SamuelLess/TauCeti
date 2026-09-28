/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.Perfect

/-! # Simple roots of squarefree polynomials

Over a perfect field, a squarefree polynomial has nonzero derivative at every
root. This supplies the pointwise simple-root premise used in root counting.
-/

public section

open Polynomial

namespace Squarefree

/-- A squarefree polynomial over a perfect field has nonzero derivative at every root. -/
theorem eval_derivative_ne_zero {K : Type*} [Field K] [PerfectField K]
    {p : K[X]} (hp : Squarefree p) {x : K} (hx : p.eval x = 0) :
    p.derivative.eval x ≠ 0 :=
  (PerfectField.separable_iff_squarefree.mpr hp).eval₂_derivative_ne_zero (RingHom.id K) hx

end Squarefree
