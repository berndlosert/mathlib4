/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval

/-! # Partial HasAntidiagonal for functions with finite support

Let `μ` be an AddCommMonoid.

In `Mathlib.Data.Finset.Antidiagonal` is defined a TypeClass
`HasAntidiagonal μ` which provides a function `μ → Finset (μ × μ)
which maps `n : μ` to a `Finset` of pairs `(a,b)`
such that `a + b = n`.

These functions apply to `ι →₀ ℕ`, more generally to `ι →₀ μ`
under the additional assumption `OrderedSub μ` that make it
a canonically ordered additive monoid.
In fact, we just need an AddMonoid with a compatible order,
finite Iic, such that if a + b = n, then a, b ≤ n,
and any other bound would be OK.

In this file, we provide an analogous definition for `ι →₀ μ`,
with an explicit finiteness condition on the support.
This Finset could be viewed inside `ι → μ`, but the `Finsupp` condition
provides a natural `DecidableEq` instance.

Consider types `ι` and `μ`, with `AddCommMonoid μ`.

* The class `Finset.HasPiAntidiagonal ι μ` provides a finite set
  `Finset.HasPiAntidiagonal.piAntidiagonal s n` of all functions
  with finite support contained in `s` and sum `n : μ`
  That condition is expressed by `HasPiAntidiagonal.mem_piAntidiagonal`
* `Finset.HasPiAntidiagonal.mem_piAntidiagonal'` rewrites the `Finsupp.sum`
  condition as a `Finset.sum`
* Assuming `Finset.HasAntidiagonal μ`, we provide a member
  `Finset.HasAntidiagonal.HasPiAntidiagonal` of that class
* The construction starts with `Finset.HasPiAntidiagonal.finAntidiagonal`,
  a variant of `Finset.Nat.antidiagonalTuple`

-/

namespace Finset

open scoped BigOperators

open Function Finsupp

section HasPiAntidiagonal

/-- The HasPiAntidiagonal class -/
class HasPiAntidiagonal (ι : Type*) (μ : Type*) [AddCommMonoid μ] where
  /-- The piAntidiagonal function -/
  piAntidiagonal : Finset ι → μ → Finset (ι →₀ μ)
  /-- A function belongs to `piAntidiagonal s n`
    iff its support is contained in s and the sum of its components is equal to `n` -/
  mem_piAntidiagonal {s} {n} {f} :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ sum f (fun _ x => x) = n

export HasPiAntidiagonal (piAntidiagonal mem_piAntidiagonal)


namespace HasPiAntidiagonal

section Fin

variable {μ : Type*} [AddCommMonoid μ] [DecidableEq μ] [HasAntidiagonal μ]

/-- `finAntidiagonal d n` is the type of d-tuples with sum n -/
noncomputable def finAntidiagonal : (d : ℕ) → μ → Finset (Fin d →₀ μ)
  | 0 => fun n => ite (n = 0) {0} ∅
  | d + 1 => fun n => by
    exact Finset.biUnion (antidiagonal n)
      (fun ab => (finAntidiagonal d ab.2).map {
        toFun := fun f => Finsupp.cons (ab.1) f
        inj' := fun f g h => by
          simp only at h
          rw [← tail_cons ab.1 f, ← tail_cons ab.1 g, h]})

lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal d n ↔ sum f (fun _ x => x) = n := by
  revert n f
  induction d with
  | zero => exact fun n f => (by
      simp only [Nat.zero_eq, finAntidiagonal, Pi.const_zero,
        Matrix.zero_empty, univ_eq_empty, sum_empty]
      by_cases hn : n = 0
      · rw [if_pos hn, hn, mem_singleton]
        simp only [eq_iff_true_of_subsingleton, true_iff]
        rw [Subsingleton.eq_zero f, sum_zero_index]
      · simp only [if_neg hn, not_mem_empty, false_iff]
        rw [Subsingleton.eq_zero f, sum_zero_index]
        exact Ne.symm hn)
  | succ d ih => exact fun n f => by (
      simp only [finAntidiagonal, mem_biUnion, mem_antidiagonal, mem_map,
        Embedding.coeFn_mk, Prod.exists]
      constructor
      · rintro ⟨a, b, hab, g, hg, hf⟩
        rw [ih b g] at hg
        rw [← hf, Finsupp.sum_cons, hg, hab]
      · intro hf
        use f 0, sum (tail f) (fun _ e => e)
        constructor
        · rw [← cons_tail f, Finsupp.sum_cons] at hf
          exact hf
        exact ⟨tail f, by rw [ih], cons_tail f⟩)

lemma mem_finAntidiagonal' (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal d n ↔ univ.sum f = n := by
  rw [mem_finAntidiagonal, sum_of_support_subset f (subset_univ _) _ (fun _ _ => rfl)]

end Fin

section

variable {ι μ : Type*}

variable [AddCommMonoid μ] [HasAntidiagonal μ] [HasPiAntidiagonal ι μ]

lemma mem_piAntidiagonal' (s : Finset ι) (n : μ) (f) :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ s.sum f = n := by
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, and_congr_right_iff]
  intro hs
  rw [sum_of_support_subset _ hs]
  exact fun _ _ => rfl

@[simp]
theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, mem_singleton, subset_empty]
  rw [support_eq_empty, and_iff_left_iff_imp]
  intro hf
  rw [hf, sum_zero_index]

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, subset_empty, support_eq_empty, sum_empty,
    not_mem_empty, iff_false, not_and]
  intro hf
  rw [hf, sum_zero_index]
  exact Ne.symm hn

theorem piAntidiagonal_empty [DecidableEq μ] (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn
  · rw [hn]
    apply piAntidiagonal_empty_of_zero
  · apply piAntidiagonal_empty_of_ne_zero hn

theorem mem_piAntidiagonal_insert [DecidableEq ι] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ piAntidiagonal (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ piAntidiagonal s m.2 := by
  simp only [mem_piAntidiagonal', le_eq_subset, mem_antidiagonal, Prod.exists]
  constructor
  · rintro ⟨hsupp, hsum⟩
    use (f a), (s.sum f)
    rw [sum_insert h] at hsum
    simp only [hsum, true_and]
    use Finsupp.erase a f
    constructor
    · ext x
      by_cases hx : x = a
      · rw [hx]
        simp only [coe_update, update_same]
      · simp only [Finsupp.update, mem_support_iff, ne_eq, not_not, support_erase, coe_mk]
        simp only [Function.update, dif_neg hx]
        simp only [Finsupp.erase, coe_mk]
        rw [if_neg hx]
    constructor
    · intro x hx
      rw [mem_support_iff] at hx
      suffices hx' : x ∈ insert a s
      rw [mem_insert] at hx'
      cases' hx' with hx' hx'
      · exfalso
        apply hx
        rw [hx']
        simp only [mem_support_iff, ne_eq, not_not, erase_same]
      · exact hx'
      apply hsupp
      rw [mem_support_iff]
      intro hx'
      apply hx
      simp only [Finsupp.erase, coe_mk, hx', ite_self]
    · apply sum_congr rfl
      intro x hx
      simp only [Finsupp.erase, coe_mk, ite_eq_left_iff, if_neg (ne_of_mem_of_not_mem hx h)]
  · rintro ⟨n1, n2, hn, g, hf, hgsupp, hgsum⟩
    constructor
    · intro x
      simp only [hf, mem_support_iff, Finset.mem_insert]
      simp only [Finsupp.coe_update, ne_eq]
      by_cases hx : x = a
      · simp only [hx, ne_eq, not_true, true_or, implies_true]
      · rw [Function.update, dif_neg hx]
        intro hx
        right
        apply hgsupp
        rw [mem_support_iff]
        exact hx
    · rw [sum_insert h, ← hn]
      apply congr_arg₂
      · simp only [hf, coe_update, update_same]
      · rw [← hgsum]
        apply sum_congr rfl
        intro x hx
        rw [hf]
        simp only [Finsupp.update, coe_mk]
        unfold Function.update
        rw [dif_neg (ne_of_mem_of_not_mem hx h)]

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq μ] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (piAntidiagonal s p.snd).attach.map
        (Set.InjOn.embedding (f := fun f => Finsupp.update f a p.fst)
        (fun f hf g hg => by
          simp only [mem_val, mem_piAntidiagonal] at hf hg
          simp only [FunLike.ext_iff]
          apply forall_imp
          intro x
          by_cases hx : x = a
          · intro _
            have : g x = 0
            · rw [← not_mem_support_iff, hx]
              exact fun hx' => h (hg.1 hx')
            rw [this]
            · rw [← not_mem_support_iff, hx]
              exact fun hx' => h (hf.1 hx')
          · simp only [coe_update, ne_eq, Function.update, dif_neg hx]
            exact id))) := by
  ext f
  rw [mem_piAntidiagonal_insert h, mem_biUnion]
  apply exists_congr
  rintro ⟨n1, n2⟩
  apply and_congr_right'
  simp only [mem_map, mem_attach, true_and, Subtype.exists]
  apply exists_congr
  intro g
  constructor
  · rintro ⟨hf, hg⟩
    use hg
    rw [hf]
    apply symm
    ext x
    simp
  · rintro ⟨hg, hf⟩
    constructor
    · ext x
      rw [← hf]
      simp
    · exact hg

-- This should work under the assumption that e is an embedding and an AddHom
lemma mapRange_piAntidiagonal_subset {μ' : Type*} [AddCommMonoid μ'] [HasPiAntidiagonal ι μ']
    {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding ⊆ piAntidiagonal s (e n) := by
  intro f
  simp only [mem_map, mem_piAntidiagonal]
  rintro ⟨g, ⟨hsupp, hsum⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe, le_eq_subset]
  constructor
  · exact subset_trans (support_mapRange) hsupp
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsupp_sum]

lemma mapRange_piAntidiagonal_eq {μ' : Type*} [AddCommMonoid μ'] [HasPiAntidiagonal ι μ']
    {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (piAntidiagonal s n).map (mapRange.addEquiv e).toEmbedding = piAntidiagonal s (e n) := by
  ext f
  constructor
  · apply mapRange_piAntidiagonal_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply mapRange_piAntidiagonal_subset
    rw [← mem_map_equiv]
    convert hf
    rw [map_map, hh]
    convert map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end

section CanonicallyOrderedAddCommMonoid

variable {ι μ : Type*} [CanonicallyOrderedAddCommMonoid μ] [HasPiAntidiagonal ι μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp only [mem_piAntidiagonal', mem_singleton, sum_eq_zero_iff, le_eq_subset]
  constructor
  · rintro ⟨hsupp, hsum⟩
    ext x
    by_cases hx : x ∈ f.support
    · exact hsum x (hsupp hx)
    · simpa only [mem_support_iff, ne_eq, not_not] using hx
  · intro hf
    simp [hf]

end CanonicallyOrderedAddCommMonoid
end HasPiAntidiagonal

section Construction

/- Here, we construct an `HasPiAntidiagonal ι μ` whenever we are given `HasAntidiagonal μ` -/

open HasPiAntidiagonal
namespace HasAntidiagonal

namespace HasPiAntidiagonal

variable {ι : Type*} [DecidableEq ι]

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ]

/-- The Finset underlying `Finset.HasAntidiagonal.HasPiAntidiagonal` -/
noncomputable def piAntidiagonal' (s : Finset ι) (n : μ) : Finset (ι →₀ μ) := by
  exact (finAntidiagonal s.card n).map {
    toFun := embDomain {
        toFun := Subtype.val.comp (equivFin s).symm,
        inj' := by
          rw [Equiv.injective_comp]
          exact Subtype.val_injective }
    inj' := embDomain_injective _ }

lemma mem_piAntidiagonal' {s : Finset ι} {n : μ} {f : ι →₀ μ} :
    f ∈ piAntidiagonal' s n ↔ f.support ≤ s ∧ Finsupp.sum f (fun _ x => x) = n := by
  simp only [piAntidiagonal', mem_map, Embedding.coeFn_mk, le_eq_subset]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_finAntidiagonal] at hf
    suffices hs : _ ≤ s
    apply And.intro hs
    rw [sum_embDomain, hf]
    · simp only [support_embDomain]
      intro i
      simp only [mem_map]
      rintro ⟨k, _, rfl⟩
      simp only [Embedding.coeFn_mk, comp_apply, coe_mem]
  · rintro ⟨hsupp, hsum⟩
    simp_rw [mem_finAntidiagonal]
    set e : Fin s.card ↪ ι :=
      Function.Embedding.trans s.equivFin.symm.toEmbedding (Embedding.subtype fun x ↦ x ∈ s) with he
    have he' : ∃ (v : Fin s.card →₀ μ), embDomain e v = f := by
      have hrange : Set.range e = s := by
        rw [he, Embedding.trans]
        simp only [Embedding.coe_subtype, Equiv.coe_toEmbedding, Embedding.coeFn_mk,
          EquivLike.range_comp, Subtype.range_coe_subtype, setOf_mem]
      rw [mem_embDomain, hrange, coe_subset]
      exact hsupp
    obtain ⟨v : Fin s.card →₀ μ, hv⟩ := he'
    use v
    constructor
    · rw [← hv] at hsum
      simp only [sum_embDomain] at hsum
      exact hsum
    · rw [← hv, he]
      rfl

end HasPiAntidiagonal

open Finset.HasAntidiagonal.HasPiAntidiagonal

/-- Given `HasAntidiagonal μ`, a definition of `HasPiAntidiagonal` -/
noncomputable def HasPiAntidiagonal {ι μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ] :
  HasPiAntidiagonal ι μ :=
{ piAntidiagonal     := piAntidiagonal'
  mem_piAntidiagonal := mem_piAntidiagonal' }

end HasAntidiagonal

end Construction

end HasPiAntidiagonal

end Finset
