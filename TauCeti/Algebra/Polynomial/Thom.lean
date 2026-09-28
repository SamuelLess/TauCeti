/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Polynomial.Rolle
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Sign.Defs

/-! # Thom sign conditions from polynomial Rolle

Sign conditions on all formal derivatives define intervals. Consequently the
signs of the positive-order derivatives distinguish roots of a nonzero
polynomial, including multiple roots. No squarefreeness assumption is needed.
The only extra premise on the ordered field is polynomial Rolle, supplied by
`TauCeti.RealClosure.polynomialRolle_of_isRealClosed` over every real closed ordered field.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Propositions 2.27 and 2.28 (Thom's lemma and root encodings).
-/

public section

open TauCeti (PolynomialRolle)

open Polynomial SignType Set

namespace Polynomial

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The sign of the `k`th formal derivative at `x`, including order zero. -/
noncomputable def derivativeSign (p : R[X]) (x : R) (k : ℕ) : SignType :=
  sign ((derivative^[k] p).eval x)

/-- Derivative signs are signs of evaluations of iterated formal derivatives. -/
theorem derivativeSign_def (p : R[X]) (x : R) (k : ℕ) :
    derivativeSign p x k = sign ((derivative^[k] p).eval x) := (rfl)

@[simp, grind =]
theorem derivativeSign_zero_left (x : R) (k : ℕ) : derivativeSign (0 : R[X]) x k = 0 := by
  simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_zero_right (p : R[X]) (x : R) :
    derivativeSign p x 0 = sign (p.eval x) := by
  simp [derivativeSign_def]

@[simp, grind =]
theorem derivativeSign_eq_zero (p : R[X]) (x : R) {k : ℕ} (hk : p.natDegree < k) :
    derivativeSign p x k = 0 := by
  simp [derivativeSign_def, iterate_derivative_eq_zero hk]

@[simp, grind =]
theorem derivativeSign_C (a x : R) (k : ℕ) :
    derivativeSign (C a) x k = if k = 0 then sign a else 0 := by
  cases k with
  | zero => simp [derivativeSign_def]
  | succ k => simp

/-- Shifting the polynomial shifts the derivative index. -/
theorem derivativeSign_iterate (p : R[X]) (x : R) (i j : ℕ) :
    derivativeSign (derivative^[i] p) x j = derivativeSign p x (j + i) := by
  simp only [derivativeSign_def, Function.iterate_add_apply]

/-- The usual finite Thom encoding retains derivatives 1 through the degree. -/
noncomputable def thomEncoding (p : R[X]) (x : R) : Fin p.natDegree → SignType :=
  fun i => derivativeSign p x (i.val + 1)

/-- Coordinate `i` records the sign of derivative `i + 1`. -/
@[simp, grind =]
theorem thomEncoding_apply (p : R[X]) (x : R) (i : Fin p.natDegree) :
    thomEncoding p x i = derivativeSign p x (i.val + 1) := (rfl)

/-- At and above the degree the derivative is constant, so its sign is
independent of the point. -/
theorem derivativeSign_const (p : R[X]) (a b : R) {k : ℕ} (hk : p.natDegree ≤ k) :
    derivativeSign p a k = derivativeSign p b k := by
  have hd : (derivative^[k] p).natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((natDegree_iterate_derivative p k).trans (by omega))
  simp only [derivativeSign_def]
  rw [eq_C_of_natDegree_eq_zero hd]
  simp

/-- A differing finite Thom coordinate lies below the top derivative,
so a next coordinate exists. -/
theorem thom_lt_degree (p : R[X]) {a b : R} {i : Fin p.natDegree}
    (hne : thomEncoding p a i ≠ thomEncoding p b i) : i.val + 1 < p.natDegree := by
  by_contra! hi
  exact hne (derivativeSign_const p a b hi)

end Basic

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

private theorem sign_between_aux (hrolle : PolynomialRolle R) (n : ℕ) (p : R[X])
    (hn : derivative^[n] p = 0) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) := by
  have hab := hx.1.trans hx.2
  induction n generalizing p x with
  | zero =>
    have hp : p = 0 := hn
    simp [hp]
  | succ n ih =>
    have hd : derivative^[n] p.derivative = 0 := by
      simpa only [Function.iterate_succ_apply] using hn
    have hs : ∀ k, derivativeSign p.derivative a k = derivativeSign p.derivative b k := by
      intro k
      simpa only [derivativeSign_def, Function.iterate_succ_apply] using h (k + 1)
    have hd_sign (y : R) (hy : y ∈ Icc a b) :
        sign (p.derivative.eval y) = sign (p.derivative.eval a) := ih p.derivative hd hy hs
    have h0 : sign (p.eval a) = sign (p.eval b) := h 0
    rcases le_total 0 (p.derivative.eval a) with hp | hp
    · have hm : MonotoneOn p.eval (Icc a b) :=
        hrolle.monotoneOn p (by
            intro y hy
            rw [← sign_nonneg_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
            exact sign_nonneg_iff.mpr hp)
      exact le_antisymm ((sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)).trans_eq h0.symm)
        (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
    · have hm : AntitoneOn p.eval (Icc a b) :=
        hrolle.antitoneOn p (by
            intro y hy
            rw [← sign_nonpos_iff, hd_sign y ⟨hy.1.le, hy.2.le⟩]
            exact sign_nonpos_iff.mpr hp)
      exact le_antisymm (sign.monotone (hm ⟨le_rfl, hab⟩ hx hx.1))
        (h0.trans_le (sign.monotone (hm hx ⟨hab, le_rfl⟩ hx.2)))

/-- Equal derivative sign conditions persist throughout the interval between
any two realizations. This includes the sign of the polynomial itself. -/
private theorem sign_between (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R} (hx : x ∈ Icc a b)
    (h : ∀ k, derivativeSign p a k = derivativeSign p b k) :
    sign (p.eval x) = sign (p.eval a) :=
  sign_between_aux hrolle (p.natDegree + 1) p (iterate_derivative_eq_zero (by omega))
    hx h

/-- Equal full derivative sign vectors agree throughout the interval between their realizations. -/
theorem derivativeSign_eq (p : R[X]) (hrolle : PolynomialRolle R) {a b x : R}
    (hx : x ∈ Icc a b) (h : derivativeSign p a = derivativeSign p b) :
    derivativeSign p x = derivativeSign p a := by
  funext k
  apply sign_between (derivative^[k] p) hrolle hx
  intro j
  simp only [derivativeSign_iterate]
  exact congrFun h (j + k)

/-- A full derivative sign condition is order-convex. Empty conditions are
allowed; this statement does not assert that an arbitrary word is realizable. -/
theorem ordConnected_derivativeSign (p : R[X]) (hrolle : PolynomialRolle R) (σ : ℕ → SignType) :
    OrdConnected (derivativeSign p ⁻¹' {σ}) := by
  constructor
  intro a ha b hb x hx
  exact (derivativeSign_eq p hrolle hx (ha.trans hb.symm)).trans ha

/-- Roots with equal signs of every positive-order derivative are equal.
The polynomial need not be squarefree. -/
theorem thom_ext (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hs : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) : a = b := by
  have h (k : ℕ) : derivativeSign p a k = derivativeSign p b k := by
    cases k with
    | zero => simp [derivativeSign_def, ha, hb]
    | succ k => exact hs _ (Nat.succ_pos _)
  have no_lt {u v : R} (hu : p.eval u = 0)
      (hσ : ∀ k, derivativeSign p u k = derivativeSign p v k) (huv : u < v) : False := by
    apply hp
    apply p.eq_zero_of_infinite_isRoot
    apply (Ioo_infinite huv).mono
    intro x hx
    have hx0 := sign_between p hrolle ⟨hx.1.le, hx.2.le⟩ hσ
    rw [hu, sign_zero, sign_eq_zero_iff] at hx0
    exact hx0
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (no_lt ha h hab).elim
  · exact hab
  · exact (no_lt hb (fun k => (h k).symm) hba).elim

/-- A finite Thom encoding uniquely identifies a root of a nonzero polynomial. -/
theorem thomEncoding_injOn (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) :
    Set.InjOn (thomEncoding p) {x | p.eval x = 0} := by
  intro a ha b hb h
  apply thom_ext p hrolle hp ha hb
  intro k hk
  by_cases hkd : k ≤ p.natDegree
  · have he := congrFun h ⟨k - 1, by omega⟩
    simpa only [thomEncoding_apply, Nat.sub_add_cancel hk] using he
  · simp [derivativeSign_eq_zero p _ (by omega : p.natDegree < k)]

private theorem sign_order_aux (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} (hab : a < b)
    (hne : sign (p.eval a) ≠ sign (p.eval b))
    (htail : ∀ k, 0 < k → derivativeSign p a k = derivativeSign p b k) :
    (sign (p.derivative.eval a) = 1 ∧ sign (p.eval a) < sign (p.eval b)) ∨
    (sign (p.derivative.eval a) = -1 ∧ sign (p.eval b) < sign (p.eval a)) := by
  have hd (x : R) (hx : x ∈ Icc a b) :
      sign (p.derivative.eval x) = sign (p.derivative.eval a) := by
    apply sign_between p.derivative hrolle hx
    intro k
    simpa only [derivativeSign_def, Function.iterate_succ_apply] using htail (k + 1) (by omega)
  rcases lt_trichotomy (p.derivative.eval a) 0 with hn | hz | hp
  · have hm : StrictAntiOn p.eval (Icc a b) :=
      hrolle.strictAntiOn p (by
        intro x hx
        rw [← sign_eq_neg_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
        exact sign_neg hn)
    exact Or.inr ⟨sign_neg hn,
      lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne.symm⟩
  · have hp0 : p.derivative = 0 := by
      apply p.derivative.eq_zero_of_infinite_isRoot
      apply (Ioo_infinite hab).mono
      intro x hx
      have h := hd x ⟨hx.1.le, hx.2.le⟩
      simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot, hz, sign_zero, sign_eq_zero_iff] using h
    have hc := eq_C_of_derivative_eq_zero hp0
    exact (hne (by rw [hc]; simp)).elim
  · have hm : StrictMonoOn p.eval (Icc a b) :=
      hrolle.strictMonoOn p (by
        intro x hx
        rw [← sign_eq_one_iff, hd x ⟨hx.1.le, hx.2.le⟩]
        exact sign_pos hp)
    exact Or.inl ⟨sign_pos hp,
      lt_of_le_of_ne (sign.monotone (hm ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le) hne⟩

/-- At the largest derivative index where signs differ, the next common sign
and the two differing signs determine the order of the points. -/
theorem thom_order (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    (a < b ↔
      (derivativeSign p a (k + 1) = 1 ∧ derivativeSign p a k < derivativeSign p b k) ∨
      (derivativeSign p a (k + 1) = -1 ∧ derivativeSign p b k < derivativeSign p a k)) := by
  have forward {u v : R} (huv : u < v)
      (hne : derivativeSign p u k ≠ derivativeSign p v k)
      (ht : ∀ j, k < j → derivativeSign p u j = derivativeSign p v j) :
      (derivativeSign p u (k + 1) = 1 ∧ derivativeSign p u k < derivativeSign p v k) ∨
      (derivativeSign p u (k + 1) = -1 ∧ derivativeSign p v k < derivativeSign p u k) := by
    have h := sign_order_aux (derivative^[k] p) hrolle huv hne (by
      intro j hj
      rw [derivativeSign_iterate, derivativeSign_iterate]
      exact ht _ (by omega))
    simpa only [derivativeSign_def, Function.iterate_succ_apply'] using h
  constructor
  · exact fun hab => forward hab hne htail
  · intro h
    rcases lt_trichotomy a b with hab | hab | hba
    · exact hab
    · subst b; exact (hne rfl).elim
    · have hrev := forward hba hne.symm (fun j hj => (htail j hj).symm)
      have heq := htail (k + 1) (by omega)
      rcases h with ⟨hpos, hlt⟩ | ⟨hneg, hlt⟩ <;>
        rcases hrev with ⟨hpos', hlt'⟩ | ⟨hneg', hlt'⟩
      · exact (lt_asymm hlt hlt').elim
      · rw [← heq, hpos] at hneg'; cases hneg'
      · rw [← heq, hneg] at hpos'; cases hpos'
      · exact (lt_asymm hlt hlt').elim

/-- The comparison rule directly on finite Thom words. `thom_lt_degree` supplies
existence of the next coordinate from the differing signs. Every coordinate
above the disagreement must agree. -/
theorem thomEncoding_order (p : R[X]) (hrolle : PolynomialRolle R) {a b : R}
    (i : Fin p.natDegree)
    (hne : thomEncoding p a i ≠ thomEncoding p b i)
    (htail : ∀ j : Fin p.natDegree, i < j → thomEncoding p a j = thomEncoding p b j) :
    (a < b ↔
      (thomEncoding p a ⟨i.val + 1, thom_lt_degree p hne⟩ = 1 ∧
        thomEncoding p a i < thomEncoding p b i) ∨
      (thomEncoding p a ⟨i.val + 1, thom_lt_degree p hne⟩ = -1 ∧
        thomEncoding p b i < thomEncoding p a i)) := by
  simp only [thomEncoding_apply] at hne ⊢
  apply thom_order p hrolle hne
  intro j hj
  by_cases hd : j ≤ p.natDegree
  · have hjpos : 1 ≤ j := by omega
    have he := htail ⟨j-1, by omega⟩ (by simp only [Fin.lt_def]; omega)
    simpa only [thomEncoding_apply, Nat.sub_add_cancel hjpos] using he
  · simp [derivativeSign_eq_zero p _ (by omega : p.natDegree < j)]

/-- The common sign immediately above the last disagreement cannot be zero. -/
theorem thom_next_nonzero (p : R[X]) (hrolle : PolynomialRolle R) {a b : R} {k : ℕ}
    (hne : derivativeSign p a k ≠ derivativeSign p b k)
    (htail : ∀ j, k < j → derivativeSign p a j = derivativeSign p b j) :
    derivativeSign p a (k + 1) ≠ 0 := by
  have hab : a ≠ b := fun h => hne (congrArg (fun x => derivativeSign p x k) h)
  rcases hab.lt_or_gt with hlt | hlt
  · rcases (thom_order p hrolle hne htail).mp hlt with h | h <;> simp [h.1]
  · have ht := fun j hj => (htail j hj).symm
    rw [htail (k + 1) (by omega)]
    rcases (thom_order p hrolle hne.symm ht).mp hlt with h | h <;> simp [h.1]

/-- Distinct roots have a last disagreement strictly below the degree.
All larger derivative signs agree, including the highest derivative sign. -/
theorem exists_thom_disagreement (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0) (hab : a ≠ b) :
    ∃ k, 0 < k ∧ k < p.natDegree ∧
      derivativeSign p a k ≠ derivativeSign p b k ∧
      ∀ j, k < j → derivativeSign p a j = derivativeSign p b j := by
  have henc : thomEncoding p a ≠ thomEncoding p b := by
    intro heq
    exact hab (thomEncoding_injOn p hrolle hp ha hb heq)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp henc
  let s := (Finset.range (p.natDegree + 1)).filter
    (fun j => derivativeSign p a j ≠ derivativeSign p b j)
  have hs : s.Nonempty := ⟨i.val + 1, by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hi⟩⟩
  let k := s.max' hs
  have hk : k ∈ s := Finset.max'_mem s hs
  have hk' := (Finset.mem_filter.mp hk).2
  have hpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    apply hk'
    simp [hk0, derivativeSign_def, ha, hb]
  have hdeg : k < p.natDegree := by
    by_contra hn
    exact hk' (derivativeSign_const p a b (by omega))
  refine ⟨k, hpos, hdeg, hk', ?_⟩
  intro j hj
  by_cases hd : p.natDegree ≤ j
  · exact derivativeSign_const p a b hd
  · by_contra hne
    have hjs : j ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hne⟩
    have hle : j ≤ k := Finset.le_max' s j hjs
    omega

/-- For distinct roots the last differing derivative index exists, the next
common sign is nonzero, and these two signs determine the root order. -/
theorem thom_root_order (p : R[X]) (hrolle : PolynomialRolle R) (hp : p ≠ 0) {a b : R}
    (ha : p.eval a = 0) (hb : p.eval b = 0) (hab : a ≠ b) :
    ∃ k, 0 < k ∧ k < p.natDegree ∧
      derivativeSign p a k ≠ derivativeSign p b k ∧
      (∀ j, k < j → derivativeSign p a j = derivativeSign p b j) ∧
      derivativeSign p a (k + 1) ≠ 0 ∧
      (a < b ↔
        (derivativeSign p a (k + 1) = 1 ∧ derivativeSign p a k < derivativeSign p b k) ∨
        (derivativeSign p a (k + 1) = -1 ∧ derivativeSign p b k < derivativeSign p a k)) := by
  obtain ⟨k, hk, hkd, hne, ht⟩ := exists_thom_disagreement p hrolle hp ha hb hab
  exact ⟨k, hk, hkd, hne, ht, thom_next_nonzero p hrolle hne ht,
    thom_order p hrolle hne ht⟩

end Polynomial
