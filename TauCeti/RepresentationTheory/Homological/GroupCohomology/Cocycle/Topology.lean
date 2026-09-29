/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Cocycle
public import Mathlib.Topology.Separation.Basic

/-!
# The zero locus of a continuous `1`-cocycle

For a `1`-cocycle `f : G → M` in the sense of Mathlib's unbundled `groupCohomology.IsCocycle₁`,
`groupCohomology.zeroLocus` is the subgroup `{g | f g = 0}` of `G`. This file records its
topological property:

* `groupCohomology.isClosed_zeroLocus`: the zero locus of a continuous `1`-cocycle with values
  in a `T1` space is closed.
-/

public section

namespace groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [MulAction G M] [TopologicalSpace G]
  [TopologicalSpace M] [T1Space M]

/-- The zero locus of a continuous `1`-cocycle with values in a `T1` space is closed. -/
theorem isClosed_zeroLocus {f : G → M} (hf : IsCocycle₁ f) (hc : Continuous f) :
    IsClosed (zeroLocus hf : Set G) := by
  rw [coe_zeroLocus]
  exact isClosed_singleton.preimage hc

end groupCohomology
