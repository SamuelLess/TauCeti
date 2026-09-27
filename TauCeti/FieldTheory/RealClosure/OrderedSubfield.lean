/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.Ordering
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-! # Ordered intermediate fields in a fixed algebraic extension

The ambient field need not be ordered. An intermediate field carries its
positive cone, allowing compatible chains of ordered fields to be united.
-/

@[expose] public section

namespace RealClosure

variable (K L : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] [Algebra K L]

/-- An ordered intermediate field whose order extends that of the base. -/
@[ext] structure OrderedSubfield where
  field : IntermediateField K L
  nonneg : Subsemiring L
  nonneg_le : ∀ x ∈ nonneg, x ∈ field
  total : ∀ x ∈ field, x ∈ nonneg ∨ -x ∈ nonneg
  neg_one : -1 ∉ nonneg
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
    change y.val * y.val ∈ P.nonneg
    rcases P.total y.val y.property with hy | hy
    · exact mul_mem hy hy
    · simpa only [neg_mul_neg] using mul_mem hy hy
  neg_one_notMem' := P.neg_one

instance (P : OrderedSubfield K L) : (preordering P).IsOrdering where
  mem_or_neg_mem x := P.total x.val x.property
  toIsPrime := inferInstance

/-- The induced linear order on the intermediate field. -/
@[instance_reducible] noncomputable def order (P : OrderedSubfield K L) :
    LinearOrder P.field := Preordering.order P.preordering

omit [IsStrictOrderedRing K] in
theorem ordered (P : OrderedSubfield K L) : letI := P.order
    IsStrictOrderedRing P.field := Preordering.ordered P.preordering

omit [IsStrictOrderedRing K] in
theorem nonneg_iff (P : OrderedSubfield K L) (x : P.field) : letI := P.order
    0 ≤ x ↔ x.val ∈ P.nonneg := Preordering.nonneg_iff P.preordering x

theorem base_strictMono (P : OrderedSubfield K L) : letI := P.order
    StrictMono (algebraMap K P.field) := by
  let := P.order
  have := P.ordered
  intro a b hab
  have hn : 0 ≤ algebraMap K P.field (b - a) :=
    (P.nonneg_iff _).mpr (P.base_nonneg (b - a) (sub_nonneg.mpr hab.le))
  have hz : algebraMap K P.field (b - a) ≠ 0 :=
    (map_ne_zero _).mpr (sub_ne_zero.mpr hab.ne')
  simpa only [map_sub, sub_pos] using lt_of_le_of_ne hn hz.symm

/-- The image of an ordered extension under an embedding into the ambient field. -/
def image {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    (hf : StrictMono (algebraMap K E)) (f : E →ₐ[K] L) : OrderedSubfield K L where
  field := f.fieldRange
  nonneg := (Subsemiring.nonneg E).map f.toRingHom
  nonneg_le := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  total := by
    rintro x ⟨y, rfl⟩
    rcases le_total 0 y with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨-y, neg_nonneg.mpr hy, map_neg f y⟩
  neg_one := by
    rintro ⟨y, hy, heq⟩
    have : y = -1 := f.injective (by simpa using heq)
    exact (not_le_of_gt zero_lt_one) (by simpa [this] using hy)
  base_nonneg x hx := ⟨algebraMap K E x, by simpa using hf.monotone hx, f.commutes x⟩

/-- The base field as an ordered intermediate field. -/
def base : OrderedSubfield K L := image (by simpa using strictMono_id) (Algebra.ofId K L)

instance : Nonempty (OrderedSubfield K L) := ⟨base⟩

/-- The union of a nonempty chain of compatible ordered intermediate fields. -/
def chainUnion (c : Set (OrderedSubfield K L)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : OrderedSubfield K L where
  field :=
    { carrier := {x | ∃ P ∈ c, x ∈ P.field}
      zero_mem' := by obtain ⟨P, hP⟩ := hne; exact ⟨P, hP, zero_mem _⟩
      one_mem' := by obtain ⟨P, hP⟩ := hne; exact ⟨P, hP, one_mem _⟩
      add_mem' := by
        rintro x y ⟨P, hP, hx⟩ ⟨Q, hQ, hy⟩
        rcases hc.total hP hQ with h | h
        · exact ⟨Q, hQ, add_mem (h.1 hx) hy⟩
        · exact ⟨P, hP, add_mem hx (h.1 hy)⟩
      mul_mem' := by
        rintro x y ⟨P, hP, hx⟩ ⟨Q, hQ, hy⟩
        rcases hc.total hP hQ with h | h
        · exact ⟨Q, hQ, mul_mem (h.1 hx) hy⟩
        · exact ⟨P, hP, mul_mem hx (h.1 hy)⟩
      inv_mem' := by rintro x ⟨P, hP, hx⟩; exact ⟨P, hP, inv_mem hx⟩
      algebraMap_mem' := by
        intro x
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hP, P.field.algebraMap_mem x⟩ }
  nonneg :=
    { carrier := {x | ∃ P ∈ c, x ∈ P.nonneg}
      zero_mem' := by obtain ⟨P, hP⟩ := hne; exact ⟨P, hP, zero_mem _⟩
      one_mem' := by obtain ⟨P, hP⟩ := hne; exact ⟨P, hP, one_mem _⟩
      add_mem' := by
        rintro x y ⟨P, hP, hx⟩ ⟨Q, hQ, hy⟩
        rcases hc.total hP hQ with h | h
        · exact ⟨Q, hQ, add_mem (h.2 hx) hy⟩
        · exact ⟨P, hP, add_mem hx (h.2 hy)⟩
      mul_mem' := by
        rintro x y ⟨P, hP, hx⟩ ⟨Q, hQ, hy⟩
        rcases hc.total hP hQ with h | h
        · exact ⟨Q, hQ, mul_mem (h.2 hx) hy⟩
        · exact ⟨P, hP, mul_mem hx (h.2 hy)⟩ }
  nonneg_le := by rintro x ⟨P, hP, hx⟩; exact ⟨P, hP, P.nonneg_le x hx⟩
  total := by
    rintro x ⟨P, hP, hx⟩
    exact (P.total x hx).imp (fun h => ⟨P, hP, h⟩) (fun h => ⟨P, hP, h⟩)
  neg_one := by rintro ⟨P, _, hp⟩; exact P.neg_one hp
  base_nonneg := by
    intro x hx
    obtain ⟨P, hP⟩ := hne
    exact ⟨P, hP, P.base_nonneg x hx⟩

omit [IsStrictOrderedRing K] in
theorem le_chainUnion (c : Set (OrderedSubfield K L)) (hc : IsChain (· ≤ ·) c)
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
  have := P.ordered
  intro hf
  have hbase : StrictMono (algebraMap K E) := by
    intro a b hab
    simpa only [← IsScalarTower.algebraMap_apply K P.field E] using hf (P.base_strictMono hab)
  let Q := image hbase (f.restrictScalars K)
  refine ⟨Q, ⟨?_, ?_⟩, fun x => ⟨x, rfl⟩⟩
  · intro x hx
    exact ⟨algebraMap P.field E ⟨x, hx⟩, f.commutes ⟨x, hx⟩⟩
  · intro x hx
    let y : P.field := ⟨x, P.nonneg_le x hx⟩
    have hy : 0 ≤ y := (P.nonneg_iff y).mpr hx
    exact ⟨algebraMap P.field E y, by simpa using hf.monotone hy, f.commutes y⟩

/-- Every element of such an extension lies in a maximal ordered intermediate field. -/
theorem mem_of_maximal (P : OrderedSubfield K L) (hP : IsMax P) {E : Type*}
    [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    [Algebra P.field E] [IsScalarTower K P.field E] (f : E →ₐ[P.field] L) :
    letI := P.order
    StrictMono (algebraMap P.field E) → ∀ x : E, f x ∈ P.field := by
  intro hf x
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_image f hf
  exact (hP hPQ).1 (hQ x)

end OrderedSubfield

end RealClosure
