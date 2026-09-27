/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Extension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Hom.Monoid

/-! # Ordered intermediate fields of a field extension

The ambient field need not be ordered. An intermediate field carries its
positive cone, allowing compatible chains of ordered fields to be united.
-/

public section

namespace TauCeti.RealClosure

variable (K L : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] [Algebra K L]

/-- An ordered intermediate field whose order extends that of the base. -/
@[ext] structure OrderedSubfield where
  /-- The underlying intermediate field. -/
  field : IntermediateField K L
  /-- The nonnegative elements, represented in the ambient field. -/
  nonneg : Subsemiring L
  nonneg_subset : ∀ x ∈ nonneg, x ∈ field
  mem_or_neg_mem : ∀ x ∈ field, x ∈ nonneg ∨ -x ∈ nonneg
  neg_one_notMem : -1 ∉ nonneg
  base_nonneg : ∀ x : K, 0 ≤ x → algebraMap K L x ∈ nonneg

namespace OrderedSubfield

variable {K L}

instance : PartialOrder (OrderedSubfield K L) :=
  PartialOrder.lift (fun P => (P.field, P.nonneg)) (by
    intro P Q h
    obtain ⟨hf, hn⟩ := Prod.mk.inj h
    exact OrderedSubfield.ext hf hn)

omit [IsStrictOrderedRing K] in
theorem le_iff (P Q : OrderedSubfield K L) :
    P ≤ Q ↔ P.field ≤ Q.field ∧ P.nonneg ≤ Q.nonneg := Iff.rfl

/-- The positive cone viewed inside its own intermediate field. -/
def preordering (P : OrderedSubfield K L) : RingPreordering P.field where
  __ := P.nonneg.comap P.field.val.toRingHom
  mem_of_isSquare' := by
    rintro x ⟨y, rfl⟩
    -- The inherited carrier field is still wrapped by `comap` in this constructor goal;
    -- reducing it exposes ambient membership. `simp [mem_comap, map_mul]` does not unfold it.
    change y.val * y.val ∈ P.nonneg
    rcases P.mem_or_neg_mem y.val y.property with hy | hy
    · exact mul_mem hy hy
    · simpa only [neg_mul_neg] using mul_mem hy hy
  neg_one_notMem' := P.neg_one_notMem

instance (P : OrderedSubfield K L) : (preordering P).IsOrdering where
  mem_or_neg_mem x := P.mem_or_neg_mem x.val x.property
  toIsPrime := inferInstance

/-- The induced linear order on the intermediate field. -/
@[instance_reducible] noncomputable def order (P : OrderedSubfield K L) :
    LinearOrder P.field := RingPreordering.order P.preordering

omit [IsStrictOrderedRing K] in
theorem isStrictOrderedRing (P : OrderedSubfield K L) : letI := P.order
    IsStrictOrderedRing P.field := RingPreordering.isStrictOrderedRing P.preordering

omit [IsStrictOrderedRing K] in
theorem nonneg_iff (P : OrderedSubfield K L) (x : P.field) : letI := P.order
    0 ≤ x ↔ x.val ∈ P.nonneg := RingPreordering.nonneg_iff P.preordering x

theorem base_strictMono (P : OrderedSubfield K L) : letI := P.order
    StrictMono (algebraMap K P.field) := by
  let := P.order
  have := P.isStrictOrderedRing
  exact ((monotone_iff_map_nonneg (algebraMap K P.field)).mpr fun x hx =>
    (P.nonneg_iff _).mpr (P.base_nonneg x hx)).strictMono_of_injective
      (algebraMap K P.field).injective

/-- The image of an ordered extension under an embedding into the ambient field. -/
def image {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    (hf : Monotone (algebraMap K E)) (f : E →ₐ[K] L) : OrderedSubfield K L where
  field := f.fieldRange
  nonneg := (Subsemiring.nonneg E).map f.toRingHom
  nonneg_subset := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  mem_or_neg_mem := by
    rintro x ⟨y, rfl⟩
    rcases le_total 0 y with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨-y, neg_nonneg.mpr hy, map_neg f y⟩
  neg_one_notMem := by
    rintro ⟨y, hy, heq⟩
    have : y = -1 := f.injective (by simpa using heq)
    exact (not_le_of_gt zero_lt_one) (by simpa [this] using hy)
  base_nonneg x hx := ⟨algebraMap K E x, by simpa using hf hx, f.commutes x⟩

/-- The base field as an ordered intermediate field. -/
def base : OrderedSubfield K L := image (by simpa using monotone_id) (Algebra.ofId K L)

instance : Nonempty (OrderedSubfield K L) := ⟨base⟩

/-- The union of a nonempty chain of compatible ordered intermediate fields. -/
private def chainUnion (c : Set (OrderedSubfield K L)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : OrderedSubfield K L := by
  have := hne.to_subtype
  have hf : Directed (· ≤ ·) (fun P : c => P.val.field) := by
    intro P Q
    rcases hc.total P.property Q.property with h | h
    · exact ⟨Q, h.1, le_rfl⟩
    · exact ⟨P, le_rfl, h.1⟩
  have hn : Directed (· ≤ ·) (fun P : c => P.val.nonneg) := by
    intro P Q
    rcases hc.total P.property Q.property with h | h
    · exact ⟨Q, h.2, le_rfl⟩
    · exact ⟨P, le_rfl, h.2⟩
  exact
    { field := (⨆ P : c, P.val.field).copy {x | ∃ P ∈ c, x ∈ P.field} (by
        rw [IntermediateField.coe_iSup_of_directed hf]
        ext x
        simp)
      nonneg := (⨆ P : c, P.val.nonneg).copy {x | ∃ P ∈ c, x ∈ P.nonneg} (by
        rw [Subsemiring.coe_iSup_of_directed hn]
        ext x
        simp)
      nonneg_subset := by rintro x ⟨P, hP, hx⟩; exact ⟨P, hP, P.nonneg_subset x hx⟩
      mem_or_neg_mem := by
        rintro x ⟨P, hP, hx⟩
        exact (P.mem_or_neg_mem x hx).imp (fun h => ⟨P, hP, h⟩) (fun h => ⟨P, hP, h⟩)
      neg_one_notMem := by rintro ⟨P, _, hp⟩; exact P.neg_one_notMem hp
      base_nonneg := by
        intro x hx
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hP, P.base_nonneg x hx⟩ }

omit [IsStrictOrderedRing K] in
private theorem le_chainUnion (c : Set (OrderedSubfield K L)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : OrderedSubfield K L} (hP : P ∈ c) :
    P ≤ chainUnion c hc hne :=
  ⟨fun _ hx => ⟨P, hP, hx⟩, fun _ hx => ⟨P, hP, hx⟩⟩

/-- There is a maximal ordered intermediate field extending the given base order. -/
theorem exists_maximal : ∃ P : OrderedSubfield K L, IsMax P :=
  zorn_le_nonempty fun c hc hne =>
    ⟨chainUnion c hc hne, fun _ hP => le_chainUnion c hc hne hP⟩

/-- An ordered extension embedded in the ambient field gives a larger ordered
intermediate field, with the original signs preserved. -/
theorem exists_image (P : OrderedSubfield K L) {E : Type*}
    [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    [Algebra P.field E] [IsScalarTower K P.field E] (f : E →ₐ[P.field] L) :
    letI := P.order
    StrictMono (algebraMap P.field E) →
      ∃ Q : OrderedSubfield K L, P ≤ Q ∧ ∀ x : E, f x ∈ Q.field := by
  let := P.order
  have := P.isStrictOrderedRing
  intro hf
  have hbase : StrictMono (algebraMap K E) := by
    intro a b hab
    simpa only [← IsScalarTower.algebraMap_apply K P.field E] using hf (P.base_strictMono hab)
  let Q := image hbase.monotone (f.restrictScalars K)
  refine ⟨Q, ⟨?_, ?_⟩, fun x => ⟨x, rfl⟩⟩
  · intro x hx
    exact ⟨algebraMap P.field E ⟨x, hx⟩, f.commutes ⟨x, hx⟩⟩
  · intro x hx
    let y : P.field := ⟨x, P.nonneg_subset x hx⟩
    have hy : 0 ≤ y := (P.nonneg_iff y).mpr hx
    exact ⟨algebraMap P.field E y, by simpa using hf.monotone hy, f.commutes y⟩

/-- Every embedding of an ordered extension of a maximal ordered intermediate field `P`
into the ambient field has its image inside `P.field`. -/
theorem mem_of_isMax (P : OrderedSubfield K L) (hP : IsMax P) {E : Type*}
    [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    [Algebra P.field E] [IsScalarTower K P.field E] (f : E →ₐ[P.field] L) :
    letI := P.order
    StrictMono (algebraMap P.field E) → ∀ x : E, f x ∈ P.field := by
  intro hf x
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_image f hf
  exact (hP hPQ).1 (hQ x)

end OrderedSubfield

end TauCeti.RealClosure
