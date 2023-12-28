/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Data.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

#align_import ring_theory.polynomial.selmer from "leanprover-community/mathlib"@"3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6"

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/


namespace Polynomial

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1
  · linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [this, pow_zero, pow_one, eq_self_iff_true, or_true_iff, true_or_iff]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow zero_lt_three).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, self_eq_add_left] at h1)
  · exact one_ne_zero (by rwa [key, self_eq_add_right] at h1)
  · exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_aux Polynomial.X_pow_sub_X_sub_one_irreducible_aux

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ', Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible Polynomial.X_pow_sub_X_sub_one_irreducible

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_X_sub_one_irreducible_rat Polynomial.X_pow_sub_X_sub_one_irreducible_rat

lemma MulAction.isPretransitive_of_compHom {E F : Type*} (G : Type*) [Monoid E] [Monoid F]
    [MulAction F G] (f : E →* F) [h : letI := MulAction.compHom G f; MulAction.IsPretransitive E G] :
    MulAction.IsPretransitive F G :=
  letI := MulAction.compHom G f; ⟨fun x y ↦ let ⟨g, hg⟩ := h.exists_smul_eq x y; ⟨f g, hg⟩⟩

lemma Set.Finite.induction'' {α : Type*} [Finite α] (P : Set α → Prop) (S0 : Set α)
    (h0 : P S0) (ih : ∀ S ≠ Set.univ, P S → ∃ a ∉ S, P ({a} ∪ S)) : P Set.univ := by
  refine' Finite.to_wellFoundedGT.wf.induction_bot' (fun T hT hT' ↦ _) h0
  obtain ⟨a, ha, ha'⟩ := ih T hT hT'
  exact ⟨_, Set.ssubset_insert ha, ha'⟩

open Equiv Pointwise

/- A transitive permutation group generated by transpositions must be the entire symmetric group -/
lemma keylemma {α : Type*} [DecidableEq α] [Finite α] (S : Set (Perm α)) (hS : ∀ σ ∈ S, σ.IsSwap)
    [MulAction.IsPretransitive (Subgroup.closure S) α] : Subgroup.closure S = ⊤ := by
  -- first separate out the case when `α` is empty
  rcases isEmpty_or_nonempty α with _ | ⟨⟨a0⟩⟩
  · apply Subsingleton.elim
  -- `P T` says that `Subgroup.closure S` contains all transpositions of elements of `T`
  let P : Set α → Prop := fun T ↦ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → swap x y ∈ Subgroup.closure S
  -- it suffices to show `P Set.univ`, since then `Subgroup.closure S` contains all transpositions
  suffices : P Set.univ
  · rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
    rintro - ⟨x, y, hxy, rfl⟩
    exact this x (Set.mem_univ x) y (Set.mem_univ y) hxy
  -- we will prove `P Set.univ` by induction, adding one element at a time
  apply Set.Finite.induction'' P ∅ (by simp)
  -- we assume `P T`, and must prove `P ({b} ∪ T)` for some `b ∉ T`
  intro T hT ih
  -- first separate out the case where `T` is empty
  rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨a0, Set.not_mem_empty a0, by simp⟩
  -- now we have `a ∈ T` and `b ∉ T`
  obtain ⟨b, hb⟩ := T.ne_univ_iff_exists_not_mem.mp hT
  -- but we can actually choose `a` and `b` so that `swap a b ∈ Subgroup.closure S`
  have key : ∃ a b, swap a b ∈ Subgroup.closure S ∧ a ∈ T ∧ b ∉ T
  · -- the action is transitive, so there is some `σ ∈ Subgroup.closure S` with `σ a = b`
    obtain ⟨⟨σ, hσ⟩, rfl⟩ := MulAction.exists_smul_eq (Subgroup.closure S) a b
    -- but then `σ` does not stabilize `T`
    have h : ¬ Subgroup.closure S ≤ MulAction.stabilizer (Perm α) T :=
      fun h ↦ ne_of_mem_of_not_mem' (Set.smul_mem_smul_set ha) hb (h hσ)
    rw [Subgroup.closure_le, Set.not_subset] at h
    -- so there must be some generator `τ` that does not stabilize `T`
    obtain ⟨τ, hτ, hτ'⟩ := h
    -- write `τ = swap x y` and bash cases on whether `x ∈ T` or `y ∈ T`
    obtain ⟨x, y, -, rfl⟩ := hS τ hτ
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
    · absurd hτ'
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem, swap_inv, Perm.smul_def, swap_apply_def]
      split_ifs <;> simp only [*]
    · exact ⟨x, y, Subgroup.subset_closure hτ, hx, hy⟩
    · exact ⟨y, x, swap_comm x y ▸ Subgroup.subset_closure hτ, hy, hx⟩
    · absurd hτ'
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem, swap_inv, Perm.smul_def, swap_apply_def]
      split_ifs <;> simp only [*]
  clear a ha b hb
  -- now we have `a ∈ T` and `b ∉ T` and `swap a b ∈ Subgroup.closure S`
  obtain ⟨a, b, hab, ha, hb⟩ := key
  refine' ⟨b, hb, _⟩
  -- we will prove `P ({b} ∪ T)` with a case bash
  rintro x (rfl | hx) y (rfl | hy) hxy
  · contradiction
  · rcases eq_or_ne y a with rfl | h
    · exact swap_comm x y ▸ hab
    rw [← swap_mul_swap_mul_swap h hxy.symm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hab (ih y hy a ha h)) hab
  · rcases eq_or_ne x a with rfl | h
    · exact swap_comm x y ▸ hab
    rw [swap_comm, ← swap_mul_swap_mul_swap h hxy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hab (ih x hx a ha h)) hab
  · exact ih x hx y hy hxy

/- A transitive permutation group generated by transpositions must be the entire symmetric group -/
lemma keylemma' {α β : Type*} [Group α] [MulAction α β] [DecidableEq β] [Finite β]
    [MulAction.IsPretransitive α β] (S : Set α)
    (hS1 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom α β σ)) (hS2 : Subgroup.closure S = ⊤) :
    Function.Surjective (MulAction.toPermHom α β) := by
  rw [← MonoidHom.range_top_iff_surjective]
  have := MulAction.isPretransitive_of_compHom β (MulAction.toPermHom α β).rangeRestrict
  rw [MonoidHom.range_eq_map, ← hS2, MonoidHom.map_closure] at this ⊢
  exact keylemma _ (Set.ball_image_iff.mpr hS1)

open IntermediateField

lemma galAction_isPretransitive {F E : Type*} [Field F] [Field E] [Algebra F E] {p : Polynomial F}
    (hp : Irreducible p) [Fact (p.Splits (algebraMap F E))] :
    MulAction.IsPretransitive p.Gal (p.rootSet E) := by
  refine' ⟨fun x y ↦ _⟩
  let ϕ := Gal.rootsEquivRoots p E
  have hx := minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet (ϕ.symm x).2)
  have hy := minpoly.eq_of_irreducible hp (aeval_eq_zero_of_mem_rootSet (ϕ.symm y).2)
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit p.SplittingField).mp (hy.symm.trans hx)
  exact ⟨g, ϕ.apply_eq_iff_eq_symm_apply.mpr (Subtype.ext hg)⟩

attribute [local instance] Gal.splits_ℚ_ℂ

instance {α β : Type*} [Monoid α] [Subsingleton β] [MulAction α β] :
    MulAction.IsPretransitive α β :=
  ⟨fun _ _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩

open NumberField

def reshom {K : Type*} [Field K] (σ : K →+* K) : 𝓞 K →+* 𝓞 K :=
  σ.restrict (𝓞 K) (𝓞 K) (fun _ ↦ map_isIntegral_int σ)

def res {K : Type*} [Field K] (σ : K ≃+* K) : 𝓞 K ≃+* 𝓞 K :=
  RingEquiv.ofHomInv (reshom σ) (reshom σ.symm)
    (by ext x; exact σ.symm_apply_apply x) (by ext x; exact σ.apply_symm_apply x)

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  let f : ℚ[X] := X ^ n - X - 1
  change Function.Bijective (Gal.galActionHom f ℂ)
  have : MulAction.IsPretransitive f.Gal (f.rootSet ℂ)
  · rcases eq_or_ne n 1 with rfl | hn
    · have : IsEmpty (rootSet f ℂ) := by simp
      infer_instance
    exact galAction_isPretransitive (X_pow_sub_X_sub_one_irreducible_rat hn)
  let K := f.SplittingField
  let R := 𝓞 K
  let S0 : Set f.Gal := ⋃ (q : Ideal R) (hq : q.IsMaximal), {σ | ∀ x : R, res σ x - x ∈ q}
  let S : Set f.Gal := S0 \ {1}
  have hS0 : Subgroup.closure S0 = ⊤
  · sorry
  have hS1 : Subgroup.closure S = ⊤
  · have h : Subgroup.closure (S0 ∩ {1}) = ⊥
    · rw [eq_bot_iff, ← Subgroup.closure_singleton_one]
      exact Subgroup.closure_mono (Set.inter_subset_right S0 {1})
    rw [← hS0, ← Set.diff_union_inter S0 {1}, Subgroup.closure_union, h, sup_bot_eq]
  have hS2 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom f.Gal (f.rootSet ℂ) σ)
  · rintro σ ⟨hσ, hσ1 : σ ≠ 1⟩
    rw [Set.mem_iUnion] at hσ
    obtain ⟨q, hσ⟩ := hσ
    rw [Set.mem_iUnion] at hσ
    obtain ⟨hq, hσ : ∀ x : R, res σ x - x ∈ q⟩ := hσ
    let F := R ⧸ q
    let π : R →+* F := Ideal.Quotient.mk q
    have : Field F := Ideal.Quotient.field q
    -- finite field, might not need to consider the characteristic
    -- reduce to action on roots in R
    sorry
  exact ⟨Gal.galActionHom_injective f ℂ, keylemma' S hS2 hS1⟩

  -- have : ∀ p : Nat.Primes, ∀ q : factors (map (algebraMap ℤ R) p)
  -- roots lie in the ring of integers OK
  -- if q is a prime idea of OK, then there is a ring homomorphism to the finite field OK/q
  -- the whole Galois group acts on OK
  -- the decomposition group acts on OK/q
  -- the inertia group acts trivially on OK/q
  --
  -- there are n roots in OK
  -- there are n or n-1 roots in OK/q (possible double root)
  -- Let σ(x) = x (mod p) for all x in OK
  -- If there are n roots in OK/q, then σ must act trivially on the roots in OK
  -- If x and y collapse (mod p), then maybe σ swaps x and y, but no more
  -- Now run through p's and σ's

  -- the key is proving closure/generating
  -- we need to know that if a subgroup contains every σ(x) = x (mod p) for every p, then it's ⊤
  -- we need to know that if a subfield is fixed by ..., then it's ⊥
  -- key facts from algebraic number theory: p divides discriminant implies ramified
  -- ramified means there exists σ(x) = x (mod p)

#check NumberField.discr_gt_one

end Polynomial
