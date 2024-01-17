/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Boolean algebra of regular open sets

This module defines regular open sets in a topological space, which are the sets `s` for which
`interior (closure s) = s`.



-/

variable {α : Type*} [TopologicalSpace α]

/--
A set `s` is regular open if `interior (closure s) = s`
-/
def IsRegularOpen (s : Set α) : Prop :=
  interior (closure s) = s

theorem isRegularOpen_iff (s : Set α) : IsRegularOpen s ↔ interior (closure s) = s := Iff.rfl

namespace IsRegularOpen

variable (α) in
theorem empty : IsRegularOpen (∅ : Set α) := by
  rw [isRegularOpen_iff, closure_empty, interior_empty]

variable (α) in
theorem univ : IsRegularOpen (Set.univ : Set α) := by
  rw [isRegularOpen_iff, closure_univ, interior_univ]

theorem of_compl_closure_of_open {s : Set α} (s_open : IsOpen s) : IsRegularOpen (closure s)ᶜ := by
  rw [isRegularOpen_iff, closure_compl, interior_compl,
    IsOpen.closure_interior_closure_eq_closure s_open]

theorem of_interior_closure (s : Set α) : IsRegularOpen (interior (closure s)) := by
  rw [closure_eq_compl_interior_compl, interior_compl]
  exact of_compl_closure_of_open isOpen_interior

/--
A regular open set is open.
-/
theorem isOpen {s : Set α} (s_reg : IsRegularOpen s) : IsOpen s := s_reg ▸ isOpen_interior

theorem compl_closure {s : Set α} (s_reg : IsRegularOpen s) : IsRegularOpen (closure s)ᶜ :=
  of_compl_closure_of_open s_reg.isOpen

theorem inter {s t : Set α} (s_reg : IsRegularOpen s) (t_reg : IsRegularOpen t) :
    IsRegularOpen (s ∩ t) := by
  rw [isRegularOpen_iff]
  apply subset_antisymm
  · apply Set.subset_inter
    · nth_rw 2 [← s_reg]
      exact interior_mono (closure_mono (Set.inter_subset_left s t))
    · nth_rw 2 [← t_reg]
      exact interior_mono (closure_mono (Set.inter_subset_right s t))
  · apply IsOpen.subset_interior_closure
    exact s_reg.isOpen.inter t_reg.isOpen

end IsRegularOpen

lemma IsOpen.interior_closure_inter {s t : Set α} (s_open : IsOpen s) :
    interior (closure (s ∩ t)) = interior (closure s) ∩ interior (closure t) := by
  apply subset_antisymm
  · apply Set.subset_inter
    all_goals apply interior_mono
    all_goals apply closure_mono
    · exact Set.inter_subset_left s t
    · exact Set.inter_subset_right s t
  · rw [Set.inter_comm]
    apply subset_trans (IsOpen.inter_interior_closure isOpen_interior)
    rw [Set.inter_comm, ← IsRegularOpen.of_interior_closure (s ∩ t)]
    apply interior_mono
    apply closure_mono
    exact IsOpen.inter_interior_closure s_open

variable (α) in
/--
The type of sets that are regular open in α.

The regular open sets in a topology form a boolean algebra, with as complement operator
`s ↦ (closure s)ᶜ` and as infimum `s ∩ t`.
-/
structure RegularOpens :=
  carrier : Set α
  regularOpen' : IsRegularOpen carrier

namespace RegularOpens

@[simp]
theorem eq_iff {r s : RegularOpens α} : r.carrier = s.carrier ↔ r = s := by
  rw [mk.injEq]

instance : SetLike (RegularOpens α) α where
  coe := carrier
  coe_injective' := fun _ _ => eq_iff.mp

@[simp]
theorem regularOpen (r : RegularOpens α) : IsRegularOpen (r : Set α) := r.regularOpen'

instance : CanLift (Set α) (RegularOpens α) RegularOpens.carrier IsRegularOpen := ⟨
  fun s s_reg => ⟨⟨s, s_reg⟩, rfl⟩⟩

instance : PartialOrder (RegularOpens α) where
  le := fun r s => r.carrier ⊆ s.carrier
  le_refl := fun r => subset_refl r.carrier
  le_trans := fun _ _ _ h₁ h₂ => subset_trans h₁ h₂
  le_antisymm := fun r s h₁ h₂ => by
    rw [← eq_iff]
    exact subset_antisymm h₁ h₂

instance : OrderBot (RegularOpens α) where
  bot := ⟨∅, IsRegularOpen.empty α⟩
  bot_le := fun r => Set.empty_subset r.carrier

@[simp]
theorem coe_bot : ((⊥ : RegularOpens α) : Set α) = ∅ := rfl

instance : OrderTop (RegularOpens α) where
  top := ⟨Set.univ, IsRegularOpen.univ α⟩
  le_top := fun r => Set.subset_univ r.carrier

@[simp]
theorem coe_top : ((⊤ : RegularOpens α) : Set α) = Set.univ := rfl

instance : SemilatticeInf (RegularOpens α) where
  inf := fun r s => ⟨
    r.carrier ∩ s.carrier,
    IsRegularOpen.inter r.regularOpen s.regularOpen⟩
  inf_le_left := fun r s => Set.inter_subset_left r.carrier s.carrier
  inf_le_right := fun r s => Set.inter_subset_right r.carrier s.carrier
  le_inf := fun _ _ _ h₁ h₂ => Set.subset_inter h₁ h₂

instance : HasCompl (RegularOpens α) where
  compl := fun s => ⟨
    (closure s.carrier)ᶜ,
    IsRegularOpen.compl_closure s.regularOpen
  ⟩

theorem coe_compl {s : RegularOpens α} : (↑(sᶜ) : Set α) = (closure ↑s)ᶜ := rfl

theorem compl_antitone : Antitone (fun s: RegularOpens α => sᶜ) := by
  intro s t s_le_t
  apply Set.compl_subset_compl.mpr
  exact closure_mono s_le_t

theorem compl_compl (s : RegularOpens α) : sᶜᶜ = s := by
  rw [← SetLike.coe_set_eq]
  show (closure (closure (s : Set α))ᶜ)ᶜ = s
  rw [closure_compl, _root_.compl_compl, s.regularOpen]

theorem compl_le_compl_iff {s t : RegularOpens α} : sᶜ ≤ tᶜ ↔ t ≤ s := by
  refine ⟨fun h => ?t_le_s, fun h => compl_antitone h⟩
  rw [← compl_compl s, ← compl_compl t]
  exact compl_antitone h

theorem compl_inj {s t : RegularOpens α} : sᶜ = tᶜ ↔ s = t := by
  refine ⟨fun h => le_antisymm ?sc_le_tc ?tc_le_sc, fun h => h ▸ rfl⟩
  all_goals rw [← compl_le_compl_iff]
  all_goals apply le_of_eq
  · exact h.symm
  · exact h

variable (α) in
theorem compl_bot : (⊥ : RegularOpens α)ᶜ = ⊤ := by
  rw [← SetLike.coe_set_eq, coe_compl, coe_bot, coe_top, closure_empty, Set.compl_empty]

variable (α) in
theorem compl_top : (⊤ : RegularOpens α)ᶜ = ⊥ := by
  rw [← compl_compl ⊥, compl_bot]

instance : SemilatticeSup (RegularOpens α) where
  sup := fun r s => (rᶜ ⊓ sᶜ)ᶜ
  le_sup_left := fun r s => by
    show r ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl r]
    apply compl_antitone
    exact inf_le_left
  le_sup_right := fun r s => by
    show s ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl s]
    apply compl_antitone
    exact inf_le_right
  sup_le := fun r s t h₁ h₂ => by
    show (rᶜ ⊓ sᶜ)ᶜ ≤ t
    rw [← compl_compl t]
    apply compl_antitone
    apply le_inf <;> apply compl_antitone
    all_goals assumption

theorem sup_def (r s : RegularOpens α) : r ⊔ s = (rᶜ ⊓ sᶜ)ᶜ := rfl

theorem coe_sup (r s : RegularOpens α) :
    (↑(r ⊔ s) : Set α) = interior (closure (↑r ∪ ↑s)) := by
  show (closure ((closure r.carrier)ᶜ ∩ (closure s.carrier)ᶜ))ᶜ =
    interior (closure (r.carrier ∪ s.carrier))
  repeat rw [← interior_compl]
  rw [← interior_inter, ← Set.compl_union, interior_compl, interior_compl, closure_compl,
    _root_.compl_compl]

theorem coe_inf (r s : RegularOpens α) : (↑(r ⊓ s) : Set α) = ↑r ∩ ↑s := rfl

@[simp]
theorem le_iff_subset (r s : RegularOpens α) : (↑r : Set α) ⊆ ↑s ↔ r ≤ s := Iff.rfl

theorem sup_inf_distrib_right (r s t : RegularOpens α) :
    r ⊔ (s ⊓ t) = (r ⊔ s) ⊓ (r ⊔ t) := by
  rw [← SetLike.coe_set_eq]
  simp only [coe_sup, coe_inf]
  rw [Set.union_inter_distrib_left, IsOpen.interior_closure_inter]
  apply IsOpen.union r.regularOpen.isOpen s.regularOpen.isOpen

instance : DistribLattice (RegularOpens α) where
  inf_le_left := fun r s => inf_le_left
  inf_le_right := fun r s => inf_le_right
  le_inf := fun r s t => le_inf
  le_sup_inf := by
    intro r s t
    rw [sup_inf_distrib_right]

lemma inf_compl_eq_bot (r : RegularOpens α) : r ⊓ rᶜ = ⊥ := by
  rw [← SetLike.coe_set_eq, RegularOpens.coe_inf, RegularOpens.coe_compl, RegularOpens.coe_bot,
    ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_right_iff_subset]
  exact subset_closure

instance : BooleanAlgebra (RegularOpens α) where
  bot_le := fun s => bot_le
  le_top := fun s => le_top
  inf_compl_le_bot := by
    intro r
    rw [le_bot_iff, RegularOpens.inf_compl_eq_bot]
  top_le_sup_compl := by
    intro r
    rw [top_le_iff, RegularOpens.sup_def, RegularOpens.compl_compl, ← RegularOpens.compl_bot,
      RegularOpens.compl_inj, inf_comm, RegularOpens.inf_compl_eq_bot]

/--
The canonical way to turn a `Set α` into a regular open set is to simply take the interior of its
closure. This operation yields the smallest regular open superset of `s` and is monotone.
-/
def fromSet (s : Set α) : RegularOpens α := ⟨
  interior (closure s),
  IsRegularOpen.of_interior_closure s⟩

@[simp]
theorem coe_fromSet (s : Set α) : (fromSet s : Set α) = interior (closure s) := rfl

@[simp]
theorem fromSet_coe (r : RegularOpens α) : fromSet (↑r : Set α) = r := by
  rw [← SetLike.coe_set_eq, coe_fromSet, r.regularOpen]

theorem fromSet_mono {s t : Set α} (s_ss_t : s ⊆ t) : fromSet s ≤ fromSet t := by
  rw [← le_iff_subset, coe_fromSet, coe_fromSet]
  exact interior_mono (closure_mono s_ss_t)

variable (α) in
theorem fromSet_monotone : Monotone (fromSet (α := α)) := fun _ _ h => fromSet_mono h

variable (α) in
theorem fromSet_surjective : Function.Surjective (fromSet (α := α)) :=
  fun r => ⟨r.carrier, fromSet_coe r⟩

end RegularOpens