/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.SturmLocal
public import TauCeti.Data.Finset.Jumps

/-! # Signed root sums for regular Sturm chains -/

public section

namespace TauCeti.Sturm

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The finite union of the zeros of all entries of a polynomial list. -/
noncomputable def zeros (cs : List (Polynomial R)) : Finset R :=
  cs.toFinset.biUnion (fun q => q.roots.toFinset)

omit [IsStrictOrderedRing R] in
theorem mem_zeros {cs : List (Polynomial R)} (hne : ∀ q ∈ cs, q ≠ 0) {x : R} :
    x ∈ zeros cs ↔ ∃ q ∈ cs, q.eval x = 0 := by
  simp only [zeros, Finset.mem_biUnion, List.mem_toFinset, Multiset.mem_toFinset]
  exact exists_congr fun q => and_congr_right fun hq => Polynomial.mem_roots (hne q hq)

namespace Regular

variable [IsRealClosed R]

/-- Moving right from a nonroot of the head changes no variations until the
next chain zero, even if an interior entry vanishes at the endpoint. -/
theorem eq_right {cs : List (Polynomial R)} (h : Regular cs) {a c : R} (hac : a < c)
    (ha : ∀ p, cs.head? = some p → p.eval a ≠ 0)
    (hz : ∀ x, a < x → x ≤ c → x ∉ zeros cs) :
    variation cs a = variation cs c := by
  symm
  refine variation_at cs c a ?_ ha (fun q hq => h.last q hq a)
    (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 a) ?_
  · intro q hq hqc
    exact hz c hac le_rfl ((mem_zeros h.nonzero).mpr ⟨q, hq, hqc⟩)
  · intro q hq hqa
    symm
    apply eval_sign_eq hac.le
    intro x hx hqx
    rcases hx.1.eq_or_lt with hax | hax
    · exact hqa (hax ▸ hqx)
    · exact hz x hax hx.2 ((mem_zeros h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The corresponding left-endpoint identity. -/
theorem eq_left {cs : List (Polynomial R)} (h : Regular cs) {c b : R} (hcb : c < b)
    (hb : ∀ p, cs.head? = some p → p.eval b ≠ 0)
    (hz : ∀ x, c ≤ x → x < b → x ∉ zeros cs) :
    variation cs c = variation cs b := by
  refine variation_at cs c b ?_ hb (fun q hq => h.last q hq b)
    (fun i q0 q1 q2 h0 h1 h2 => h.alternate i q0 q1 q2 h0 h1 h2 b) ?_
  · intro q hq hqc
    exact hz c le_rfl hcb ((mem_zeros h.nonzero).mpr ⟨q, hq, hqc⟩)
  · intro q hq hqb
    apply eval_sign_eq hcb.le
    intro x hx hqx
    rcases hx.2.eq_or_lt with hxb | hxb
    · exact hqb (hxb ▸ hqx)
    · exact hz x hx.1 hxb ((mem_zeros h.nonzero).mpr ⟨q, hq, hqx⟩)

/-- The signed variation formula with endpoints away from every chain zero. -/
theorem sum_of_regular_endpoints {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs))
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0)
    {a b : R} (hab : a < b) (ha : a ∉ zeros (p :: q :: cs))
    (hb : b ∉ zeros (p :: q :: cs)) :
    (variation (p :: q :: cs) a : ℤ) - variation (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  classical
  let chain := p :: q :: cs
  let w : R → ℤ := fun r => if p.eval r = 0 then
    (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) else 0
  have hsum := Finset.sum_jumps (zeros chain) (fun x => (variation chain x : ℤ)) w
    (fun a b hab hn => by
      congr 1
      apply variation_const chain hab.le
      intro s hs x hx hz
      exact hn x ((mem_zeros h.nonzero).mpr ⟨s, hs, hz⟩) hx)
    (fun a r b har hrb _ hn => by
      have hz : ∀ s ∈ chain, ∀ x ∈ Set.Icc a b, x ≠ r → s.eval x ≠ 0 := by
        intro s hs x hx hxr hsx
        exact hxr (hn x ((mem_zeros h.nonzero).mpr ⟨s, hs, hsx⟩) hx)
      by_cases hr : p.eval r = 0
      · simpa [w, hr] using h.root_jump har hrb hr (hsimple r hr) (h.second_ne hr) hz
      · have hsame := h.interior har hrb (fun s hs => by cases hs; exact hr) hz
        simp only [w, chain, ite_eq_right hr, hsame.1.trans hsame.2, sub_self]) hab ha hb
  rw [hsum]
  let A := p.roots.toFinset.filter (fun r => a < r ∧ r < b)
  let B := (zeros chain).filter (fun r => a < r ∧ r < b)
  have hAB : A ⊆ B := by
    intro r hr
    obtain ⟨hr, hi⟩ := Finset.mem_filter.mp hr
    have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp))).mp
      (Multiset.mem_toFinset.mp hr)
    exact Finset.mem_filter.mpr ⟨(mem_zeros h.nonzero).mpr ⟨p, by simp, hpr⟩, hi⟩
  have hrestrict : ∑ r ∈ A, w r = ∑ r ∈ B, w r := by
    apply Finset.sum_subset hAB
    intro r hr hn
    have hpr : p.eval r ≠ 0 := by
      intro hz
      apply hn
      exact Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
        ((Polynomial.mem_roots (h.nonzero p (by simp))).mpr hz),
        (Finset.mem_filter.mp hr).2⟩
    simp [w, hpr]
  rw [← hrestrict]
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : p.eval r = 0 := (Polynomial.mem_roots (h.nonzero p (by simp))).mp
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hr).1)
  simp [w, hpr]

/-- The signed Sturm formula on an interval whose endpoints are not roots of
the head polynomial. Interior entries may vanish at either endpoint. -/
theorem sum {p q : Polynomial R} {cs : List (Polynomial R)}
    (h : Regular (p :: q :: cs))
    (hsimple : ∀ r, p.eval r = 0 → p.derivative.eval r ≠ 0)
    {a b : R} (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    (variation (p :: q :: cs) a : ℤ) - variation (p :: q :: cs) b =
      ∑ r ∈ p.roots.toFinset.filter (fun r => a < r ∧ r < b),
        (SignType.sign (p.derivative.eval r * q.eval r) : ℤ) := by
  classical
  let chain := p :: q :: cs
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  obtain ⟨c, hac, hcm, hc⟩ := Finset.exists_right_gap (zeros chain) ham
  obtain ⟨d, hmd, hdb, hd⟩ := Finset.exists_left_gap (zeros chain) hmb
  have hcd := hcm.trans hmd
  have hcZ : c ∉ zeros chain := fun hz => (hc c hz hac).false
  have hdZ : d ∉ zeros chain := fun hz => (hd d hz hdb).false
  have haV : variation chain a = variation chain c :=
    h.eq_right hac (fun s hs => by cases hs; exact ha)
      (fun x hax hxc hx => (hc x hx hax).not_ge hxc)
  have hbV : variation chain d = variation chain b :=
    h.eq_left hdb (fun s hs => by cases hs; exact hb)
      (fun x hdx hxb hx => (hd x hx hxb).not_ge hdx)
  have hfilters : p.roots.toFinset.filter (fun r => a < r ∧ r < b) =
      p.roots.toFinset.filter (fun r => c < r ∧ r < d) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, har, hrb⟩
      have hrZ : r ∈ zeros chain := (mem_zeros h.nonzero).mpr
        ⟨p, by simp, (Polynomial.mem_roots (h.nonzero p (by simp))).mp
          (Multiset.mem_toFinset.mp hr)⟩
      exact ⟨hr, hc r hrZ har, hd r hrZ hrb⟩
    · rintro ⟨hr, hcr, hrd⟩
      exact ⟨hr, hac.trans hcr, hrd.trans hdb⟩
  rw [hfilters]
  -- Fold the local chain abbreviation to match the endpoint comparison equalities.
  change (variation chain a : ℤ) - variation chain b = _
  rw [haV, ← hbV]
  exact h.sum_of_regular_endpoints hsimple hcd hcZ hdZ

end Regular

end TauCeti.Sturm
