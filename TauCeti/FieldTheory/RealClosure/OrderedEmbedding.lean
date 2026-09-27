/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.SimpleRing.Basic

/-! # Order preservation for embeddings of real closed fields

An embedding out of a real closed ordered field preserves its order because
nonnegative elements are squares. This does not construct a real closure.
-/

public section

namespace TauCeti.RealClosure

variable {R S : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] [Ring S] [LinearOrder S] [IsStrictOrderedRing S]

/-- Every field embedding from a real closed ordered field preserves order. -/
theorem embedding_strictMono (f : R →+* S) : StrictMono f :=
  (ringHom_monotone (fun _ h => IsSquare.of_nonneg h) f).strictMono_of_injective f.injective

/-- Such an embedding preserves the exact ternary sign. -/
theorem embedding_sign (f : R →+* S) (x : R) :
    SignType.sign (f x) = SignType.sign x :=
  (embedding_strictMono f).sign_comp x

end TauCeti.RealClosure
