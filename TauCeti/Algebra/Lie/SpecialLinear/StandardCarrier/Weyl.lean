/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.PointsFunctor
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Weyl
import TauCeti.Algebra.Algebra.Hom

/-!
# Simple Weyl representatives in the type-`A` carrier

At the Bourbaki node `i` of the type `A_r` carrier `TauCeti.SlStd.groupScheme r`, the numbered
root subgroups `x_{α_i}` and `x_{-α_i}` give the Weyl representative

```text
n_i = x_{α_i}(1) x_{-α_i}(-1) x_{α_i}(1),
```

a point of the carrier over every commutative ring (`TauCeti.SlStd.simpleWeylPoint`). Conjugation
by `n_i` interchanges the two root subgroups at `i`, negating the parameter, reflects the weight
torus by the root `α_i`, and so normalizes the torus.

In rank one the representative is explicit: it is the matrix with entries `0, 1; -1, 0`, it
satisfies the Chevalley relation `n² = h(-1)` for the torus point `h(s) = diag(s, s⁻¹)`, and over a
nontrivial ring its class in the pointwise normalizer quotient of the torus has order exactly two.

## Main declarations

* `TauCeti.SlStd.simpleWeylPoint`: the Weyl representative at a node, as a carrier point.
* `TauCeti.SlStd.simpleWeylPoint_conj_rootSubgroupPoints`: `n_i x_{α_i}(u) n_i⁻¹ = x_{-α_i}(-u)`.
* `TauCeti.SlStd.simpleWeylPoint_conj_weightTorusPoints` and
  `TauCeti.SlStd.simpleWeylPoint_mem_normalizer`: `n_i` reflects and normalizes the weight torus.
* `TauCeti.SlStd.coe_simpleWeylPoint_zero_apply`: the rank-one representative's matrix entries.
* `TauCeti.SlStd.simpleWeylPoint_zero_sq`: the rank-one Chevalley relation `n² = h(-1)`.
* `TauCeti.SlStd.orderOf_simpleWeylClass_zero`: in rank one, the class of the representative in
  the torus normalizer quotient has order two over a nontrivial ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace TauCeti.SlStd

open TauCeti.UniversalEnvelopingAlgebra

universe u v

attribute [local instance high] Algebra.toModule
attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- The points of the type `A_r` carrier are the points of the generic Kostant toral closure it is
cut out from. -/
theorem points_eq_kostantToralPointsSubgroup (A : Type v) [CommRing A] :
    points r A =
      kostantToralPointsSubgroup (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A := by
  rw [points_def, kostantToralPointsSubgroup_def, definingIdeal_def]

/-- The standard representation carries the numbered `sl₂` triple at node `i` to an `sl₂` triple
of endomorphisms of the standard module. -/
theorem isSl2Triple_rep (i : Fin r) :
    IsSl2Triple (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (cartanGenerator r i)))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inl i))))
      (rep r (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator r (.inr i)))) := by
  refine (isSl2Triple_rootGenerator r i).map
    ((rep r).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) fun hzero => ?_
  have h := congrFun (DFunLike.congr_fun hzero (Pi.single i.castSucc 1)) i.castSucc
  simp only [LieHom.comp_apply, AlgHom.toLieHom_apply, rep_ι_apply, val_cartanGenerator,
    LinearMap.zero_apply, Pi.zero_apply] at h
  simp [(Fin.castSucc_lt_succ (i := i)).ne'] at h

/-- **The Weyl representative at the node `i`**: `x_{α_i}(1) x_{-α_i}(-1) x_{α_i}(1)`, as a point of
the type `A_r` carrier. -/
noncomputable def simpleWeylPoint (i : Fin r) (A : Type v) [CommRing A] : points r A :=
  (MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup r A)).symm
    (kostantToralWeylPoint (rootGenerator r) (cartanGenerator r) (rep r)
      (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (.inl i) (.inr i) A)

/-- In the coordinate basis, the Weyl representative is the matrix of the integral Weyl
automorphism of the standard lattice. -/
theorem coe_simpleWeylPoint (i : Fin r) (A : Type v) [CommRing A] :
    (simpleWeylPoint r i A : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      Units.map (LinearMap.toMatrixAlgEquiv ((latticeBasis r).baseChange A)).toMulEquiv
        (kostantWeylGL (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r (.inl i)) (isNilpotent_rep_rootGenerator r (.inr i))
          A) := by
  rw [simpleWeylPoint, MulEquiv.subgroupCongr_symm_apply, coe_kostantToralWeylPoint]

/-- The Weyl representative is natural in the ring of points. -/
@[simp]
theorem map_simpleWeylPoint (i : Fin r) {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    (pointsPresentation r A).map (pointsPresentation r B) φ (simpleWeylPoint r i A) =
      simpleWeylPoint r i B := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map]
  simp only [simpleWeylPoint, MulEquiv.subgroupCongr_symm_apply]
  have hmap := congrArg Subtype.val
    (map_kostantToralWeylPoint (rootGenerator r) (cartanGenerator r) (rep r)
      (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) φ (.inl i) (.inr i))
  simpa only [GeneralLinear.coe_mapHopfIdealPointsSubgroup, MulEquiv.subgroupCongr_apply,
    RingHom.toIntAlgHom_toRingHom] using hmap

/-- **Conjugation by the Weyl representative at `i` interchanges the root subgroups at `i`**:
`n_i x_{α_i}(u) n_i⁻¹ = x_{-α_i}(-u)`. -/
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin r) (A : Type v) [CommRing A] (u : A) :
    simpleWeylPoint r i A * rootSubgroupPoints r (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint r i A)⁻¹ =
      rootSubgroupPoints r (.inr i) A (Multiplicative.ofAdd (-u)) := by
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_rootSubgroupPoints (wt := weight r) (i := .inl i) (j := .inr i)
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (isNilpotent_rep_rootGenerator r)
      (latticeBasis r) (isSl2Triple_rep r i) A u)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint, coe_rootSubgroupPoints,
    coe_kostantToralWeylPoint, coe_kostantToralRootSubgroupPoints] using hconj

private theorem lie_cartanGenerator_rootGenerator_inr (i q : Fin r) :
    ⁅cartanGenerator r q, rootGenerator r (.inr i)⁆ =
      -(((rootGeneratorWeight r (.inl i) q : ℤ) : ℚ) • rootGenerator r (.inr i)) := by
  rw [lie_cartanGenerator_rootGenerator, rootGeneratorWeight_inr, rootGeneratorWeight_inl,
    Int.cast_neg, neg_smul]

/-- **Conjugation by the Weyl representative at `i` reflects the weight torus** by the root
`α_i`. -/
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin r) (A : Type v) [CommRing A]
    (s : Fin r → Aˣ) :
    simpleWeylPoint r i A * weightTorusPoints r A s * (simpleWeylPoint r i A)⁻¹ =
      weightTorusPoints r A (weylReflectTorusPoint (rootGeneratorWeight r (.inl i)) i s) := by
  have hconj := congrArg Subtype.val
    (kostantToralWeylPoint_conj_weightTorusPoints (wt := weight r) (i := .inl i) (j := .inr i)
      (c := i) (α := rootGeneratorWeight r (.inl i)) (rootGenerator r) (cartanGenerator r)
      (rep r) (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (isSl2Triple_rep r i)
      (fun q => lie_cartanGenerator_rootGenerator r (.inl i) q)
      (lie_cartanGenerator_rootGenerator_inr r i) (isCartanWeightVector_latticeBasis r) A s)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint, coe_weightTorusPoints,
    coe_kostantToralWeylPoint, coe_kostantToralWeightTorusPoints] using hconj

/-- The Weyl representative at `i` normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer (i : Fin r) (A : Type v) [CommRing A] :
    simpleWeylPoint r i A ∈ Subgroup.normalizer
      (((weightTorusPoints r A).range : Subgroup (points r A)) : Set (points r A)) := by
  let carrierEquiv : points r A ≃*
      kostantToralPointsSubgroup (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A :=
    MulEquiv.subgroupCongr (points_eq_kostantToralPointsSubgroup r A)
  have htorusPoint (s : Fin r → Aˣ) :
      carrierEquiv (weightTorusPoints r A s) =
        kostantToralWeightTorusPoints (rootGenerator r) (cartanGenerator r) (rep r)
          (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
          (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A s := by
    apply Subtype.ext
    simp only [carrierEquiv, MulEquiv.subgroupCongr_apply]
    rw [coe_weightTorusPoints, coe_kostantToralWeightTorusPoints]
  have htorus : (weightTorusPoints r A).range.map carrierEquiv.toMonoidHom =
      (kostantToralWeightTorusPoints (rootGenerator r) (cartanGenerator r) (rep r)
        (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
        (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) A).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, (htorusPoint s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨weightTorusPoints r A s, ⟨s, rfl⟩, htorusPoint s⟩
  rw [← Subgroup.mem_map_iff_mem (f := carrierEquiv.toMonoidHom) carrierEquiv.injective,
    Subgroup.map_equiv_normalizer_eq, htorus]
  simpa [simpleWeylPoint, carrierEquiv] using
    (kostantToralWeylPoint_mem_normalizer_weightTorusPoints (i := .inl i) (j := .inr i)
      (c := i) (α := rootGeneratorWeight r (.inl i)) (rootGenerator r) (cartanGenerator r)
      (rep r) (lattice r).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (isSl2Triple_rep r i)
      (fun q => lie_cartanGenerator_rootGenerator r (.inl i) q)
      (lie_cartanGenerator_rootGenerator_inr r i) (isCartanWeightVector_latticeBasis r) A)

/-! ## Rank one -/

private theorem exp_rep_rootGenerator (k : Fin 1 ⊕ Fin 1) :
    IsNilpotent.exp (rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 k))) =
      1 + rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 k)) := by
  rw [IsNilpotent.exp_eq_sum (pow_two_rep_rootGenerator_eq_zero 1 k)]
  simp [Finset.sum_range_succ]

private theorem exp_neg_rep_rootGenerator (k : Fin 1 ⊕ Fin 1) :
    IsNilpotent.exp (-rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 k))) =
      1 - rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 k)) := by
  have hsq : (-rep 1 (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGenerator 1 k))) ^ 2 = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [pow_two, Module.End.mul_apply, LinearMap.neg_apply, LinearMap.neg_apply, map_neg, neg_neg,
      rep_rootGenerator_rep_rootGenerator_eq_zero, LinearMap.zero_apply]
  rw [IsNilpotent.exp_eq_sum hsq]
  simp [Finset.sum_range_succ, sub_eq_add_neg]

/-- In rank one, the Weyl element sends the coordinate vector `e_j` to `± e_{1 - j}`. -/
private theorem weylUnit_apply_single (j : Fin 2) :
    ((weylUnit (isNilpotent_rep_rootGenerator 1 (.inl 0))
        (isNilpotent_rep_rootGenerator 1 (.inr 0)) : (Module.End ℚ (Fin 2 → ℚ))ˣ) :
          Module.End ℚ (Fin 2 → ℚ)) (Pi.single j 1) =
      ((-1 : ℚ) ^ (1 - (j : ℕ))) • Pi.single j.rev 1 := by
  rw [coe_weylUnit, exp_rep_rootGenerator, exp_neg_rep_rootGenerator]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    map_add, map_sub, rep_rootGenerator_apply]
  fin_cases j <;> simp

private theorem kostantWeylRestrict_latticeBasis (j : Fin 2) :
    kostantWeylRestrict (rootGenerator 1) (cartanGenerator 1) (rep 1) (lattice 1).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice 1 hu hv)
        (isNilpotent_rep_rootGenerator 1 (.inl 0)) (isNilpotent_rep_rootGenerator 1 (.inr 0))
        (latticeBasis 1 j) =
      ((-1 : ℤ) ^ (1 - (j : ℕ))) • latticeBasis 1 j.rev := by
  apply Subtype.ext
  rw [coe_kostantWeylRestrict_apply, AddSubgroupClass.coe_zsmul, coe_latticeBasis,
    coe_latticeBasis, ← Int.cast_smul_eq_zsmul ℚ]
  push_cast
  exact weylUnit_apply_single j

/-- **The rank-one Weyl representative is the matrix `0, 1; -1, 0`**: its `(i, j)` entry is
`(-1) ^ i` when `i` is the reversal of `j`, and zero otherwise. -/
@[simp]
theorem coe_simpleWeylPoint_zero_apply (A : Type v) [CommRing A] (i j : Fin 2) :
    ((simpleWeylPoint 1 0 A : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) i j =
      if i = j.rev then (-1 : A) ^ (i : ℕ) else 0 := by
  rw [coe_simpleWeylPoint, Units.coe_map]
  -- The mapped unit's value is definitionally the basis matrix of its underlying endomorphism.
  change (LinearMap.toMatrixAlgEquiv ((latticeBasis 1).baseChange A)
    (kostantWeylGL (rootGenerator 1) (cartanGenerator 1) (rep 1) (lattice 1).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice 1 hu hv)
      (isNilpotent_rep_rootGenerator 1 (.inl 0)) (isNilpotent_rep_rootGenerator 1 (.inr 0))
      A).val) i j = _
  rw [kostantWeylGL_val, LinearMap.toMatrixAlgEquiv_apply, Module.Basis.baseChange_apply,
    LinearEquiv.coe_coe, kostantWeylPoints_apply_tmul, kostantWeylRestrict_latticeBasis]
  fin_cases i <;> fin_cases j <;> simp

private theorem weight_one_zero : weight 1 0 = ![1] := by
  funext q
  fin_cases q
  simp

private theorem weight_one_one : weight 1 1 = ![-1] := by
  funext q
  fin_cases q
  simp

private theorem torusCharacter_fin_one {A : Type*} [CommRing A] (s : Fin 1 → Aˣ) (n : ℤ) :
    torusCharacter s ![n] = s 0 ^ n := by
  rw [torusCharacter_def]
  simp

/-- In rank one, the torus point `h(s)` is the diagonal matrix `diag(s, s⁻¹)`. -/
theorem coe_weightTorusPoints_one_apply (A : Type v) [CommRing A] (s : Fin 1 → Aˣ)
    (i j : Fin 2) :
    ((weightTorusPoints 1 A s : Matrix.GeneralLinearGroup (Fin 2) A) :
        Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then ((s 0 ^ (if i = 0 then (1 : ℤ) else -1) : Aˣ) : A) else 0 := by
  rw [coe_weightTorusPoints, kostantTorusMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [diagGL_apply, weight_one_zero, weight_one_one, torusCharacter_fin_one]

/-- **The rank-one Chevalley relation `n² = h(-1)`.** -/
@[simp]
theorem simpleWeylPoint_zero_sq (A : Type v) [CommRing A] :
    simpleWeylPoint 1 0 A ^ 2 = weightTorusPoints 1 A (fun _ ↦ -1) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_weightTorusPoints_one_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_weightTorusPoints_one_neg_one (A : Type v) [CommRing A] :
    (weightTorusPoints 1 A (fun _ ↦ -1) : Matrix.GeneralLinearGroup (Fin 2) A) = -1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [coe_weightTorusPoints_one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- In rank one, conjugation by the Weyl representative sends the negative root subgroup to the
positive one, negating the parameter: `n x_{-α}(u) n⁻¹ = x_α(-u)`. -/
theorem simpleWeylPoint_zero_conj_rootSubgroupPoints_inr (A : Type v) [CommRing A] (u : A) :
    simpleWeylPoint 1 0 A * rootSubgroupPoints 1 (.inr 0) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint 1 0 A)⁻¹ =
      rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd (-u)) := by
  have hzero := simpleWeylPoint_conj_rootSubgroupPoints 1 0 A (-u)
  rw [neg_neg] at hzero
  let n := simpleWeylPoint 1 0 A
  let z := weightTorusPoints 1 A (fun _ ↦ -1)
  let x := rootSubgroupPoints 1 (.inl 0) A (Multiplicative.ofAdd (-u))
  -- `z` is the central element `-1`.
  have hcomm : z * x = x * z := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_weightTorusPoints_one_neg_one, neg_one_mul,
      mul_neg_one]
  rw [← hzero]
  calc
    n * (n * x * n⁻¹) * n⁻¹ = n ^ 2 * x * (n ^ 2)⁻¹ := by
      rw [pow_two]
      group
    _ = z * x * z⁻¹ := by rw [simpleWeylPoint_zero_sq]
    _ = x := by rw [hcomm]; group

/-- In rank one, conjugation by the Weyl representative inverts the torus: `n h(s) n⁻¹ = h(s⁻¹)`.
-/
theorem simpleWeylPoint_zero_conj_weightTorusPoints (A : Type v) [CommRing A] (s : Fin 1 → Aˣ) :
    simpleWeylPoint 1 0 A * weightTorusPoints 1 A s * (simpleWeylPoint 1 0 A)⁻¹ =
      weightTorusPoints 1 A (fun _ ↦ (s 0)⁻¹) := by
  rw [simpleWeylPoint_conj_weightTorusPoints]
  congr 1
  funext q
  have hq : q = 0 := Subsingleton.elim _ _
  subst hq
  have hα : rootGeneratorWeight 1 (.inl 0) = ![2] := by
    funext q
    fin_cases q
    simp [CartanMatrix.A]
  rw [weylReflectTorusPoint_apply_same, hα, torusCharacter_fin_one]
  group

/-! ## The rank-one normalizer class -/

/-- The Weyl representative at `i`, as a point of the normalizer of the weight torus. -/
noncomputable def simpleWeylNormalizerPoint (i : Fin r) (A : Type v) [CommRing A] :
    Subgroup.normalizer
      (((weightTorusPoints r A).range : Subgroup (points r A)) : Set (points r A)) :=
  ⟨simpleWeylPoint r i A, simpleWeylPoint_mem_normalizer r i A⟩

@[simp]
theorem coe_simpleWeylNormalizerPoint (i : Fin r) (A : Type v) [CommRing A] :
    (simpleWeylNormalizerPoint r i A : points r A) = simpleWeylPoint r i A :=
  (rfl)

/-- The class of the Weyl representative at `i` in the normalizer quotient of the weight torus. -/
noncomputable def simpleWeylClass (i : Fin r) (A : Type v) [CommRing A] :
    Subgroup.normalizerQuotient (weightTorusPoints r A).range :=
  Subgroup.normalizerQuotientMk _ (simpleWeylNormalizerPoint r i A)

/-- In rank one, the Weyl class has square one. -/
@[simp]
theorem simpleWeylClass_zero_sq (A : Type v) [CommRing A] : simpleWeylClass 1 0 A ^ 2 = 1 := by
  rw [simpleWeylClass, ← map_pow]
  apply (Subgroup.normalizerQuotientMk_eq_one_iff _ _).mpr
  have hsquare : simpleWeylPoint 1 0 A ^ 2 ∈ (weightTorusPoints 1 A).range := by
    rw [simpleWeylPoint_zero_sq]
    exact ⟨fun _ ↦ -1, rfl⟩
  simpa only [Subgroup.coe_pow, coe_simpleWeylNormalizerPoint] using hsquare

/-- Over a nontrivial ring, the rank-one Weyl representative is not a torus point. -/
theorem simpleWeylPoint_zero_notMem_range (A : Type v) [CommRing A] [Nontrivial A] :
    simpleWeylPoint 1 0 A ∉ (weightTorusPoints 1 A).range := by
  rintro ⟨s, hs⟩
  have hentry := congrArg
    (fun g : points 1 A ↦ ((g : Matrix.GeneralLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) 0 1) hs
  rw [coe_weightTorusPoints_one_apply, coe_simpleWeylPoint_zero_apply] at hentry
  simp at hentry

/-- Over a nontrivial ring, the rank-one Weyl class is not the identity. -/
theorem simpleWeylClass_zero_ne_one (A : Type v) [CommRing A] [Nontrivial A] :
    simpleWeylClass 1 0 A ≠ 1 := by
  intro hclass
  rw [simpleWeylClass] at hclass
  have hm := (Subgroup.normalizerQuotientMk_eq_one_iff _ _).mp hclass
  exact simpleWeylPoint_zero_notMem_range A
    (by simpa only [coe_simpleWeylNormalizerPoint] using hm)

/-- **Over a nontrivial ring, the rank-one Weyl class has order exactly two** in the normalizer
quotient of the weight torus. -/
@[simp]
theorem orderOf_simpleWeylClass_zero (A : Type v) [CommRing A] [Nontrivial A] :
    orderOf (simpleWeylClass 1 0 A) = 2 :=
  orderOf_eq_prime (simpleWeylClass_zero_sq A) (simpleWeylClass_zero_ne_one A)

end TauCeti.SlStd
