/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn

/-!
# Topological spaces with no isolated points

A topological space has no isolated point if `𝓝 p ⊓ 𝓟 {p}ᶜ ≠ ⊥` for every point `p`.
-/

open Topology

/--
A topological space has no isolated point if `𝓝 p ⊓ 𝓟 {p}ᶜ ≠ ⊥` for every point `p`.
-/
@[deprecated]
class NoIsolatedPoints (α : Type*) [TopologicalSpace α] : Prop :=
  /-- The punctured neighborhood of every point is non-bot. -/
  not_isolated' : ∀ p : α, Filter.NeBot (𝓝[≠] p)

variable {α β: Type*} [TopologicalSpace α] [TopologicalSpace β]

instance NoIsolatedPoints.not_isolated [NoIsolatedPoints α] (p : α): Filter.NeBot (𝓝[≠] p) :=
  NoIsolatedPoints.not_isolated' p

theorem nhdsWithin_punctured_prod_neBot_iff {p : α} {q : β} : Filter.NeBot (𝓝[≠] (p, q)) ↔
    Filter.NeBot (𝓝[≠] p) ∨ Filter.NeBot (𝓝[≠] q) := by
  rw [← Set.singleton_prod_singleton, Set.compl_prod_eq_union, nhdsWithin_union,
    nhdsWithin_prod_eq, nhdsWithin_univ, nhdsWithin_prod_eq, nhdsWithin_univ, Filter.neBot_iff,
    ne_eq, sup_eq_bot_iff, Filter.prod_eq_bot, Filter.prod_eq_bot, not_and_or, not_or, not_or]
  constructor
  · intro h
    cases h with
    | inl h => left; exact ⟨h.left⟩
    | inr h => right; exact ⟨h.right⟩
  · intro h
    cases h with
    | inl h => left; exact ⟨h.ne, (nhds_neBot (x := q)).ne⟩
    | inr h => right; exact ⟨(nhds_neBot (x := p)).ne, h.ne⟩

variable (α β) in
instance NoIsolatedPoints.prod_left [NoIsolatedPoints α] : NoIsolatedPoints (α × β) where
  not_isolated' := by
    intro ⟨p, q⟩
    rw [nhdsWithin_punctured_prod_neBot_iff]
    left
    exact NoIsolatedPoints.not_isolated p

variable (α β) in
instance NoIsolatedPoints.prod_right [NoIsolatedPoints β] : NoIsolatedPoints (α × β) where
  not_isolated' := by
    intro ⟨p, q⟩
    rw [nhdsWithin_punctured_prod_neBot_iff]
    right
    exact NoIsolatedPoints.not_isolated q
