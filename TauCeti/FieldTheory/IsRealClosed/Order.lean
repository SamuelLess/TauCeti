/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.SimpleRing.Basic

/-! # Order preservation for homomorphisms from real closed fields

A ring homomorphism from an ordered real closed field into an ordered ring is strictly monotone:
nonnegative elements are squares, and a field homomorphism is injective. Combined with
`Polynomial.sign_eval_map`, this transports polynomial evaluation signs along such a homomorphism.
-/

public section

namespace RingHom

/-- A ring homomorphism from an ordered real closed field into an ordered ring
is strictly monotone. -/
theorem strictMono_of_isRealClosed {R S : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S]
    (f : R →+* S) : StrictMono f :=
  (ringHom_monotone (fun _ h => IsSquare.of_nonneg h) f).strictMono_of_injective f.injective

end RingHom
