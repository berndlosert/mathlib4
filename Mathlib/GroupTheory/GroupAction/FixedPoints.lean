/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Dynamics.PeriodicPts
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.GroupAction.Period

/-!
# Properties of `fixedPoints` and `fixedBy`

This module contains some useful properties of `MulAction.fixedPoints` and `MulAction.fixedBy`
that don't directly belong to `Mathlib.GroupTheory.GroupAction.Basic`.

## Main theorems

* `MulAction.fixedBy_mul`: `fixedBy α (g * h) ⊆ fixedBy α g ∪ fixedBy α h`
* `MulAction.fixedBy_conj` and `MulAction.smul_fixedBy`: the pointwise group action of `h` on
  `fixedBy α g` is equal to the `fixedBy` set of the conjugation of `h` with `g`
  (`fixedBy α (h * g * h⁻¹)`).
* `MulAction.set_mem_fixedBy_of_movedBy_subset` shows that if a set `s` is a superset of
  `(fixedBy α g)ᶜ`, then the group action of `g` cannot send elements of `s` outside of `s`.
  This is expressed as `s ∈ fixedBy (Set α) g`, and `MulAction.set_mem_fixedBy_iff` allows one
  to convert the relationship back to `g • x ∈ s ↔ x ∈ s`.
* `MulAction.not_commute_of_disjoint_smul_movedBy` allows one to prove that `g` and `h`
  do not commute from the disjointness of the `(fixedBy α g)ᶜ` set and `h • (fixedBy α g)ᶜ`,
  which is a property used in the proof of Rubin's theorem.

The theorems above are also available for `AddAction`.

## Pointwise group action and `fixedBy (Set α) g`

Since `fixedBy α g = { x | g • x = x }` by definition, properties about the pointwise action of
a set `s : Set α` can be expressed using `fixedBy (Set α) g`.
To properly use theorems using `fixedBy (Set α) g`, you should `open Pointwise` in your file.

`s ∈ fixedBy (Set α) g` means that `g • s = s`, which is equivalent to say that
`∀ x, g • x ∈ s ↔ x ∈ s` (the translation can be done using `MulAction.set_mem_fixedBy_iff`).

`s ∈ fixedBy (Set α) g` is a weaker statement than `s ⊆ fixedBy α g`: the latter requires that
all points in `s` are fixed by `g`, whereas the former only requires that `g • x ∈ s`.
-/

namespace MulAction
open Pointwise

variable {α : Type*}
variable {G : Type*} [Group G] [MulAction G α]
variable {M : Type*} [Monoid M] [MulAction M α]


section FixedPoints

variable (α) in
/-- In a multiplicative group action, the points fixed by `g` are also fixed by `g⁻¹` -/
@[to_additive (attr := simp)
  "In an additive group action, the points fixed by `g` are also fixed by `g⁻¹`"]
theorem fixedBy_inv_eq_fixedBy (g : G) : fixedBy α g⁻¹ = fixedBy α g := by
  ext x
  rw [mem_fixedBy, mem_fixedBy, inv_smul_eq_iff, eq_comm]

@[to_additive]
theorem smul_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [mem_fixedBy, smul_left_cancel_iff]
  rfl

@[to_additive]
theorem smul_inv_mem_fixedBy_iff_mem_fixedBy {a : α} {g : G} :
    g⁻¹ • a ∈ fixedBy α g ↔ a ∈ fixedBy α g := by
  rw [← fixedBy_inv_eq_fixedBy, smul_mem_fixedBy_iff_mem_fixedBy, fixedBy_inv_eq_fixedBy]

@[to_additive period_eq_one_of_fixedBy]
theorem period_eq_one_of_fixedBy {a : α} {g : G} (a_in_fixedBy : a ∈ fixedBy α g) :
    period g a = 1 := period_eq_one_of_fixed a_in_fixedBy

variable (α) in
@[to_additive]
theorem fixedBy_subset_fixedBy_zpow (g : G) (j : ℤ) :
    fixedBy α g ⊆ fixedBy α (g ^ j) := by
  intro a a_in_fixedBy
  rw [mem_fixedBy, zpow_smul_eq_iff_period_dvd,
    period_eq_one_of_fixed a_in_fixedBy, Nat.cast_one]
  exact one_dvd j

variable (α) in
@[to_additive]
theorem fixedBy_zpow_subset_of_dvd (g : G) {j k : ℤ} (dvd : j ∣ k):
    fixedBy α (g ^ j) ⊆ fixedBy α (g ^ k) := by
  intro a a_in_fixedBy
  let ⟨n, eq⟩ := dvd
  rw [eq, zpow_mul]
  apply fixedBy_subset_fixedBy_zpow
  exact a_in_fixedBy

variable (M α) in
@[to_additive (attr := simp)]
theorem fixedBy_one_eq_univ : fixedBy α (1 : M) = Set.univ :=
  Set.eq_univ_iff_forall.mpr (fun a => one_smul M a)

variable (α) in
@[to_additive]
theorem fixedBy_mul (m₁ m₂ : M) : fixedBy α m₁ ∩ fixedBy α m₂ ⊆ fixedBy α (m₁ * m₂) := by
  intro a ⟨h₁, h₂⟩
  rw [mem_fixedBy, mul_smul, h₂, h₁]

variable (α) in
@[to_additive]
theorem fixedBy_conj (g h : G) :
    fixedBy α (h * g * h⁻¹) = (fun a => h⁻¹ • a) ⁻¹' fixedBy α g := by
  ext a
  rw [Set.mem_preimage, mem_fixedBy, mem_fixedBy]
  repeat rw [mul_smul]
  exact smul_eq_iff_eq_inv_smul h

variable (α) in
@[to_additive]
theorem smul_fixedBy (g h: G) :
    h • fixedBy α g = fixedBy α (h * g * h⁻¹) := by
  rw [fixedBy_conj, Set.preimage_smul, inv_inv]

variable (α) in
theorem fixedBy_commutatorElement (g h : G) :
    fixedBy α h ∩ g • fixedBy α h ⊆ fixedBy α ⁅g, h⁆ := by
  rw [smul_fixedBy, commutatorElement_def, Set.inter_comm, ← fixedBy_inv_eq_fixedBy α (g := h)]
  apply fixedBy_mul α

end FixedPoints

section Pointwise

/-!
### `fixedBy` sets of the pointwise group action

The theorems below need the `Pointwise` scoped to be opened (using `open Pointwise`)
to be used effectively.
-/

/--
If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in `s` after being
moved by `g`.
-/
@[to_additive "If a set `s : Set α` is in `fixedBy (Set α) g`, then all points of `s` will stay in
`s` after being moved by `g`."]
theorem set_mem_fixedBy_iff (s : Set α) (g : G) :
    s ∈ fixedBy (Set α) g ↔ ∀ x, x ∈ s ↔ g • x ∈ s := by
  constructor
  · intro fixed x
    refine ⟨
      fun x_in_s => fixed ▸ Set.smul_mem_smul_set x_in_s,
      fun gx_in_s => ?inv_in_set⟩
    rwa [← fixed, Set.smul_mem_smul_set_iff] at gx_in_s
  · intro closed
    rw [← fixedBy_inv_eq_fixedBy]
    ext x
    rw [Set.mem_inv_smul_set_iff]
    exact ⟨fun gxs => (closed x).mpr gxs, fun xs => (closed x).mp xs⟩

theorem smul_mem_of_set_mem_fixedBy {s : Set α} {g : G} (s_in_fixedBy : s ∈ fixedBy (Set α) g)
    {x : α} : x ∈ s ↔ g • x ∈ s := (set_mem_fixedBy_iff s g).mp s_in_fixedBy x

/--
If `s ⊆ fixedBy α g`, then `g • s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g • x ≠ x` and `g • x ∈ s`).
-/
@[to_additive "If `s ⊆ fixedBy α g`, then `g +ᵥ s = s`, which means that `s ∈ fixedBy (Set α) g`.

Note that the reverse implication is in general not true, as `s ∈ fixedBy (Set α) g` is a
weaker statement (it allows for points `x ∈ s` for which `g +ᵥ x ≠ x` and `g +ᵥ x ∈ s`)."]
theorem set_mem_fixedBy_of_subset_fixedBy {s : Set α} {g : G} (s_ss_fixedBy : s ⊆ fixedBy α g) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv_eq_fixedBy]
  ext x
  rw [Set.mem_inv_smul_set_iff]
  constructor
  · intro gxs
    rw [← fixedBy_inv_eq_fixedBy] at s_ss_fixedBy
    rwa [← s_ss_fixedBy gxs, inv_smul_smul] at gxs
  · intro xs
    rwa [← s_ss_fixedBy xs] at xs

theorem smul_subset_of_set_mem_fixedBy {s t : Set α} {g : G} (t_ss_s : t ⊆ s)
    (s_in_fixedBy : s ∈ fixedBy (Set α) g) : g • t ⊆ s := by
  intro x x_in_gt
  rw [Set.mem_smul_set_iff_inv_smul_mem] at x_in_gt
  apply t_ss_s at x_in_gt
  rw [← fixedBy_inv_eq_fixedBy] at s_in_fixedBy
  rwa [← s_in_fixedBy, Set.smul_mem_smul_set_iff] at x_in_gt

/-!
If a set `s : Set α` is a superset of `(MulAction.fixedBy α g)ᶜ` (resp. `(AddAction.fixedBy α g)ᶜ`),
then no point or subset of `s` can be moved outside of `s` by the group action of `g`.
-/

/-- If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`. -/
@[to_additive "If `(fixedBy α g)ᶜ ⊆ s`, then `g` cannot move a point of `s` outside of `s`."]
theorem set_mem_fixedBy_of_movedBy_subset {s : Set α} {g : G} (s_subset : (fixedBy α g)ᶜ ⊆ s) :
    s ∈ fixedBy (Set α) g := by
  rw [← fixedBy_inv_eq_fixedBy]
  ext a
  rw [Set.mem_inv_smul_set_iff]
  by_cases a ∈ fixedBy α g
  case pos a_fixed =>
    rw [a_fixed]
  case neg a_moved =>
    constructor
    all_goals (intro; apply s_subset)
    · exact a_moved
    · rwa [Set.mem_compl_iff, smul_mem_fixedBy_iff_mem_fixedBy]

/--
If the action of `f` does not move points of `s` outside of `s`, and `g • s` is disjoint from `s`,
then all points of `s` are fixed by `g * f * g⁻¹`.
-/
theorem subset_fixedBy_conj_of_movedBy_subset_of_disj {f g : G} {s : Set α}
    (superset : (fixedBy α f)ᶜ ⊆ s) (disj : Disjoint s (g • s)) : s ⊆ fixedBy α (g * f * g⁻¹) := by
  rw [← smul_fixedBy, ← Set.compl_subset_compl, ← Set.smul_set_compl]
  apply subset_trans _ disj.subset_compl_left
  exact Set.smul_set_mono superset

/--
If all points of `s` are fixed by `g * f * g⁻¹`, then `⁅f, g⁆ • s = f • s`
-/
lemma commutatorElement_smul_eq_of_subset_fixedBy_conj {f g : G} {s : Set α}
    (subset : s ⊆ fixedBy α (g * f * g⁻¹)) : ⁅f, g⁆ • s = f • s := by
  rw [commutatorElement_def]
  repeat rw [mul_smul]
  rw [smul_left_cancel_iff]
  repeat rw [← mul_smul]
  rw [← smul_fixedBy, ← fixedBy_inv_eq_fixedBy, smul_fixedBy] at subset
  exact set_mem_fixedBy_of_subset_fixedBy subset


end Pointwise

section Commute

/-!
## Pointwise image of the `fixedBy` set by a commuting group element

If two group elements `g` and `h` commute, then `g` fixes `h • x` (resp. `h +ᵥ x`)
if and only if `g` fixes `x`.

This is equivalent to say that if `Commute g h`, then `fixedBy α g ∈ fixedBy (Set α) h` and
`(fixedBy α g)ᶜ ∈ fixedBy (Set α) h`.
-/

/--
If `g` and `h` commute, then `g` fixes `h • x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
-/
@[to_additive "If `g` and `h` commute, then `g` fixes `h +ᵥ x` iff `g` fixes `x`.
This is equivalent to say that the set `fixedBy α g` is fixed by `h`.
"]
theorem fixedBy_mem_fixedBy_of_commute {g h : G} (comm: Commute g h) :
    (fixedBy α g) ∈ fixedBy (Set α) h := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_fixedBy, ← mul_smul, comm.inv_right, mul_smul,
    smul_left_cancel_iff, mem_fixedBy]

/--
If `g` and `h` commute, then `g` fixes `(h^j) • x` iff `g` fixes `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` fixes `(j • h) +ᵥ x` iff `g` fixes `x`."]
theorem smul_zpow_fixedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ):
    h^j • fixedBy α g = fixedBy α g :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (fixedBy_mem_fixedBy_of_commute comm)

/--
If `g` and `h` commute, then `g` moves `h • x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `h +ᵥ x` iff `g` moves `x`.
This is equivalent to say that the set `(fixedBy α g)ᶜ` is fixed by `h`."]
theorem movedBy_mem_fixedBy_of_commute {g h : G} (comm: Commute g h) :
    (fixedBy α g)ᶜ ∈ fixedBy (Set α) h := by
  rw [mem_fixedBy, Set.compl_eq_univ_diff, Set.smul_set_sdiff,
    Set.smul_set_univ, fixedBy_mem_fixedBy_of_commute comm]

/--
If `g` and `h` commute, then `g` moves `h^j • x` iff `g` moves `x`.
-/
@[to_additive "If `g` and `h` commute, then `g` moves `(j • h) +ᵥ x` iff `g` moves `x`."]
theorem smul_zpow_movedBy_eq_of_commute {g h : G} (comm : Commute g h) (j : ℤ):
    h ^ j • (fixedBy α g)ᶜ = (fixedBy α g)ᶜ :=
  fixedBy_subset_fixedBy_zpow (Set α) h j (movedBy_mem_fixedBy_of_commute comm)

end Commute

section Faithful

variable [FaithfulSMul G α]
variable [FaithfulSMul M α]

/-- If the multiplicative action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`. -/
@[to_additive "If the additive action of `M` on `α` is faithful,
then `fixedBy α m = Set.univ` implies that `m = 1`."]
theorem fixedBy_eq_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1 := by
  constructor
  · intro moved_empty
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    intro a
    rw [one_smul]
    by_contra ma_ne_a
    rw [← mem_fixedBy, moved_empty] at ma_ne_a
    exact ma_ne_a (Set.mem_univ a)
  · intro eq_one
    rw [eq_one]
    exact movedBy_one_eq_empty α M

@[to_additive]
theorem fixedBy_univ_iff_eq_one {m : M} : fixedBy α m = Set.univ ↔ m = 1 := by
  rw [fixedBy_eq_compl_movedBy, ← Set.compl_empty, compl_inj_iff, movedBy_empty_iff_eq_one]

/--
If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute.
-/
@[to_additive "If the image of the `(fixedBy α g)ᶜ` set by the pointwise action of `h: G`
is disjoint from `(fixedBy α g)ᶜ`, then `g` and `h` cannot commute."]
theorem not_commute_of_disjoint_movedBy_preimage {g h : G} (ne_one : g ≠ 1)
    (disjoint : Disjoint (fixedBy α g)ᶜ (h • (fixedBy α g)ᶜ)) : ¬Commute g h := by
  intro comm
  rw [movedBy_mem_fixedBy_of_commute comm, disjoint_self, Set.bot_eq_empty, ← Set.compl_univ,
    compl_inj_iff, fixedBy_eq_univ_iff_eq_one] at disjoint
  exact ne_one disjoint

variable (α) in
/--
If the action is faithful, then `g` and `h` commute if `(fixedBy α g)ᶜ` is disjoint from
`(fixedBy α h)ᶜ`.
-/
theorem commute_of_disjoint_movedBy {g h : G} (disjoint : Disjoint (fixedBy α g)ᶜ (fixedBy α h)ᶜ) :
    Commute g h := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro a
  rw [mul_smul, mul_smul]

  by_cases a_fixed : a ∈ fixedBy α g
  rw [Set.disjoint_compl_left_iff_subset] at disjoint
  swap
  have a_fixed := Set.disjoint_compl_right_iff_subset.mp disjoint a_fixed
  rw [Set.disjoint_compl_right_iff_subset] at disjoint

  all_goals {
    rw [a_fixed]
    rw [← fixedBy_inv_eq_fixedBy] at disjoint
    rw [← set_mem_fixedBy_of_movedBy_subset disjoint, Set.mem_inv_smul_set_iff] at a_fixed
    rw [a_fixed]
  }

end Faithful

end MulAction
