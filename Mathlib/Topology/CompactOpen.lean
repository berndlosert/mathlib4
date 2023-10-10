/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.SubsetProperties
import Mathlib.Topology.Maps

#align_import topology.compact_open from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `CompactOpen` is the compact-open topology on `C(X, Y)`. It is declared as an instance.
* `ContinuousMap.coev` is the coevaluation map `Y → C(X, Y × X)`. It is always continuous.
* `ContinuousMap.curry` is the currying map `C(X × Y, Z) → C(X, C(Y, Z))`. This map always exists
  and it is continuous as long as `X × Y` is locally compact.
* `ContinuousMap.uncurry` is the uncurrying map `C(X, C(Y, Z)) → C(X × Y, Z)`. For this map to
  exist, we need `Y` to be locally compact. If `X` is also locally compact, then this map is
  continuous.
* `Homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))`. This homeomorphism exists if `X` and `Y` are locally compact.


## Tags

compact-open, curry, function space
-/


open Set

open Topology

namespace ContinuousMap

section CompactOpen

variable {X : Type*} {Y : Type*} {Z : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A generating set for the compact-open topology (when `s` is compact and `u` is open). -/
def CompactOpen.gen (s : Set X) (u : Set Y) : Set C(X, Y) :=
  { f | f '' s ⊆ u }
#align continuous_map.compact_open.gen ContinuousMap.CompactOpen.gen

@[simp]
theorem gen_empty (u : Set Y) : CompactOpen.gen (∅ : Set X) u = Set.univ :=
  Set.ext fun f => iff_true_intro ((congr_arg (· ⊆ u) (image_empty f)).mpr u.empty_subset)
#align continuous_map.gen_empty ContinuousMap.gen_empty

@[simp]
theorem gen_univ (s : Set X) : CompactOpen.gen s (Set.univ : Set Y) = Set.univ :=
  Set.ext fun f => iff_true_intro (f '' s).subset_univ
#align continuous_map.gen_univ ContinuousMap.gen_univ

@[simp]
theorem gen_inter (s : Set X) (u v : Set Y) :
    CompactOpen.gen s (u ∩ v) = CompactOpen.gen s u ∩ CompactOpen.gen s v :=
  Set.ext fun _ => subset_inter_iff
#align continuous_map.gen_inter ContinuousMap.gen_inter

@[simp]
theorem gen_union (s t : Set X) (u : Set Y) :
    CompactOpen.gen (s ∪ t) u = CompactOpen.gen s u ∩ CompactOpen.gen t u :=
  Set.ext fun f => (iff_of_eq (congr_arg (· ⊆ u) (image_union f s t))).trans union_subset_iff
#align continuous_map.gen_union ContinuousMap.gen_union

theorem gen_empty_right {s : Set X} (h : s.Nonempty) : CompactOpen.gen s (∅ : Set Y) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => (h.image _).not_subset_empty
#align continuous_map.gen_empty_right ContinuousMap.gen_empty_right

-- The compact-open topology on the space of continuous maps X → Y.
instance compactOpen : TopologicalSpace C(X, Y) :=
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set X) (_ : IsCompact s) (u : Set Y) (_ : IsOpen u), m = CompactOpen.gen s u }
#align continuous_map.compact_open ContinuousMap.compactOpen

/-- Definition of `ContinuousMap.compactOpen` in terms of `Set.image2`. -/
theorem compactOpen_eq : @compactOpen X Y _ _ =
    .generateFrom (Set.image2 CompactOpen.gen {s | IsCompact s} {t | IsOpen t}) :=
  congr_arg TopologicalSpace.generateFrom <| Set.ext fun _ ↦ by simp [eq_comm]

protected theorem isOpen_gen {s : Set X} (hs : IsCompact s) {u : Set Y} (hu : IsOpen u) :
    IsOpen (CompactOpen.gen s u) :=
  TopologicalSpace.GenerateOpen.basic _ (by dsimp [mem_setOf_eq]; tauto)
#align continuous_map.is_open_gen ContinuousMap.isOpen_gen

section Functorial

variable (g : C(Y, Z))

private theorem preimage_gen {s : Set X} {u : Set Z} :
    ContinuousMap.comp g ⁻¹' CompactOpen.gen s u = CompactOpen.gen s (g ⁻¹' u) := by
  ext ⟨f, _⟩
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u
  rw [image_comp, image_subset_iff]

/-- C(X, -) is a functor. -/
theorem continuous_comp : Continuous (ContinuousMap.comp g : C(X, Y) → C(X, Z)) :=
  continuous_generateFrom fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, preimage_gen g]; exact ContinuousMap.isOpen_gen hs (hu.preimage g.2)
#align continuous_map.continuous_comp ContinuousMap.continuous_comp

/-- If `g : C(Y, Z)` is a topology inducing map, then the composition
`ContinuousMap.comp g : C(X, Y) → C(X, Z)` is a topology inducing map too. -/
theorem inducing_comp (hg : Inducing g) : Inducing (g.comp : C(X, Y) → C(X, Z)) where
  induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, preimage_gen,
      hg.setOf_isOpen, image2_image_right]

/-- If `g : C(Y, Z)` is a topological embedding, then the composition
`ContinuousMap.comp g : C(X, Y) → C(X, Z)` is an embedding too. -/
theorem embedding_comp (hg : Embedding g) : Embedding (g.comp : C(X, Y) → C(X, Z)) :=
  ⟨inducing_comp g hg.1, fun _ _ ↦ (cancel_left hg.2).1⟩

variable (f : C(X, Y))

private theorem image_gen {s : Set X} (_ : IsCompact s) {u : Set Z} (_ : IsOpen u) :
    (fun g : C(Y, Z) => g.comp f) ⁻¹' CompactOpen.gen s u = CompactOpen.gen (f '' s) u := by
  ext ⟨g, _⟩
  change g ∘ f '' s ⊆ u ↔ g '' (f '' s) ⊆ u
  rw [Set.image_comp]

/-- C(-, Z) is a functor. -/
theorem continuous_comp_left : Continuous (fun g => g.comp f : C(Y, Z) → C(X, Z)) :=
  continuous_generateFrom fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, image_gen f hs hu]
    exact ContinuousMap.isOpen_gen (hs.image f.2) hu
#align continuous_map.continuous_comp_left ContinuousMap.continuous_comp_left

/-- Composition is a continuous map from `C(X, Y) × C(Y, Z)` to `C(X, Z)`, provided that `Y` is
  locally compact. This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*. -/
theorem continuous_comp' [LocallyCompactSpace Y] :
    Continuous fun x : C(X, Y) × C(Y, Z) => x.2.comp x.1 :=
  continuous_generateFrom
    (by
      rintro M ⟨K, hK, U, hU, rfl⟩
      conv =>
        congr
        rw [CompactOpen.gen, preimage_setOf_eq]
        --congr
        ext; dsimp [setOf]
        rw [image_comp, image_subset_iff]
      rw [isOpen_iff_forall_mem_open]
      rintro ⟨φ₀, ψ₀⟩ H
      obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between (hK.image φ₀.2) (hU.preimage ψ₀.2) H
      use { φ : C(X, Y) | φ '' K ⊆ interior L } ×ˢ { ψ : C(Y, Z) | ψ '' L ⊆ U }
      -- porting note: typing hint `: φ '' K ⊆ interior L` wasn't previously required
      use fun ⟨φ, ψ⟩ ⟨(hφ : φ '' K ⊆ interior L), hψ⟩ =>
        subset_trans hφ (interior_subset.trans <| image_subset_iff.mp hψ)
      use (ContinuousMap.isOpen_gen hK isOpen_interior).prod (ContinuousMap.isOpen_gen hL hU)
      exact mem_prod.mpr ⟨hKL, image_subset_iff.mpr hLU⟩)
#align continuous_map.continuous_comp' ContinuousMap.continuous_comp'

theorem continuous.comp' [LocallyCompactSpace Y] {f : X → C(X, Y)}
    {g : X → C(Y, Z)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prod_mk hg : Continuous fun x => (f x, g x))
#align continuous_map.continuous.comp' ContinuousMap.continuous.comp'

end Functorial

section Ev

/-- The evaluation map `C(X, Y) × X → Y` is continuous if `X` is locally compact.

See also `ContinuousMap.continuous_eval` -/
theorem continuous_eval' [LocallyCompactSpace X] : Continuous fun p : C(X, Y) × X => p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨f, x⟩ n hn =>
    let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn
    have : v ∈ 𝓝 (f x) := IsOpen.mem_nhds vo fxv
    let ⟨s, hs, sv, sc⟩ :=
      LocallyCompactSpace.local_compact_nhds x (f ⁻¹' v) (f.continuous.tendsto x this)
    let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs
    show (fun p : C(X, Y) × X => p.1 p.2) ⁻¹' n ∈ 𝓝 (f, x) from
      let w := CompactOpen.gen s v ×ˢ u
      have : w ⊆ (fun p : C(X, Y) × X => p.1 p.2) ⁻¹' n := fun ⟨f', x'⟩ ⟨hf', hx'⟩ =>
        vn <| hf' <| mem_image_of_mem f' (us hx')
        --Porting note: The following `calc` block fails here.
        --calc
        --  f' x' ∈ f' '' s := mem_image_of_mem f' (us hx')
        --  _ ⊆ v := hf'
        --  _ ⊆ n := vn

      have : IsOpen w := (ContinuousMap.isOpen_gen sc vo).prod uo
      have : (f, x) ∈ w := ⟨image_subset_iff.mpr sv, xu⟩
      mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩
#align continuous_map.continuous_eval' ContinuousMap.continuous_eval'

/-- Evaluation of a continuous map `f` at a point `x` is continuous in `f`.

Porting note: merged `continuous_eval_const` with `continuous_eval_const'` removing unneeded
assumptions. -/
@[continuity]
theorem continuous_eval_const (x : X) :
    Continuous fun f : C(X, Y) => f x := by
  refine continuous_def.2 fun U hU ↦ ?_
  convert ContinuousMap.isOpen_gen (isCompact_singleton (a := x)) hU using 1
  ext; simp [CompactOpen.gen]
#align continuous_map.continuous_eval_const' ContinuousMap.continuous_eval_const
#align continuous_map.continuous_eval_const ContinuousMap.continuous_eval_const

/-- Coercion from `C(X, Y)` with compact-open topology to `X → Y` with pointwise convergence
topology is a continuous map.

Porting note: merged `continuous_coe` with `continuous_coe'` removing unneeded assumptions. -/
theorem continuous_coe : Continuous ((⇑) : C(X, Y) → (X → Y)) :=
  continuous_pi continuous_eval_const
#align continuous_map.continuous_coe' ContinuousMap.continuous_coe
#align continuous_map.continuous_coe ContinuousMap.continuous_coe

instance [T0Space Y] : T0Space C(X, Y) :=
  t0Space_of_injective_of_continuous FunLike.coe_injective continuous_coe

instance [T1Space Y] : T1Space C(X, Y) :=
  t1Space_of_injective_of_continuous FunLike.coe_injective continuous_coe

instance [T2Space Y] : T2Space C(X, Y) :=
  .of_injective_continuous FunLike.coe_injective continuous_coe

end Ev

section InfInduced

theorem compactOpen_le_induced (s : Set X) :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) ≤
      TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen := by
  simp only [induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro b ⟨a, ⟨c, hc, u, hu, rfl⟩, rfl⟩
  refine' ⟨(↑) '' c, hc.image continuous_subtype_val, u, hu, _⟩
  ext f
  simp only [CompactOpen.gen, mem_setOf_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f ((↑) : s → X)]
#align continuous_map.compact_open_le_induced ContinuousMap.compactOpen_le_induced

/-- The compact-open topology on `C(X, Y)` is equal to the infimum of the compact-open topologies
on `C(s, Y)` for `s` a compact subset of `X`.  The key point of the proof is that the union of the
compact subsets of `X` is equal to the union of compact subsets of the compact subsets of `X`. -/
theorem compactOpen_eq_sInf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) =
      ⨅ (s : Set X) (_ : IsCompact s),
        TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen := by
  refine' le_antisymm _ _
  · refine' le_iInf₂ _
    exact fun s _ => compactOpen_le_induced s
  simp only [← generateFrom_iUnion, induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro _ ⟨s, hs, u, hu, rfl⟩
  rw [mem_iUnion₂]
  refine' ⟨s, hs, _, ⟨univ, isCompact_iff_isCompact_univ.mp hs, u, hu, rfl⟩, _⟩
  ext f
  simp only [CompactOpen.gen, mem_setOf_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f ((↑) : s → X)]
  simp
#align continuous_map.compact_open_eq_Inf_induced ContinuousMap.compactOpen_eq_sInf_induced

/-- For any subset `s` of `X`, the restriction of continuous functions to `s` is continuous as a
function from `C(X, Y)` to `C(s, Y)` with their respective compact-open topologies. -/
theorem continuous_restrict (s : Set X) : Continuous fun F : C(X, Y) => F.restrict s := by
  rw [continuous_iff_le_induced]
  exact compactOpen_le_induced s
#align continuous_map.continuous_restrict ContinuousMap.continuous_restrict

theorem nhds_compactOpen_eq_sInf_nhds_induced (f : C(X, Y)) :
    𝓝 f = ⨅ (s) (hs : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compactOpen_eq_sInf_induced]
  simp [nhds_iInf, nhds_induced]
#align continuous_map.nhds_compact_open_eq_Inf_nhds_induced ContinuousMap.nhds_compactOpen_eq_sInf_nhds_induced

theorem tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι → C(X, Y)} {f : C(X, Y)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set X) :
    Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).continuousAt.tendsto.comp hFf
#align continuous_map.tendsto_compact_open_restrict ContinuousMap.tendsto_compactOpen_restrict

theorem tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι → C(X, Y)) (f : C(X, Y)) :
    Filter.Tendsto F l (𝓝 f) ↔
    ∀ (s) (hs : IsCompact s), Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) := by
    rw [compactOpen_eq_sInf_induced]
    simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp]
#align continuous_map.tendsto_compact_open_iff_forall ContinuousMap.tendsto_compactOpen_iff_forall

/-- A family `F` of functions in `C(X, Y)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `X`. -/
theorem exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace X] [T2Space Y]
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι → C(X, Y)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
    ∀ (s : Set X) (hs : IsCompact s), ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) := by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : X) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      haveI := isCompact_iff_compactSpace.mp hs₁
      haveI := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs
#align continuous_map.exists_tendsto_compact_open_iff_forall ContinuousMap.exists_tendsto_compactOpen_iff_forall

end InfInduced

section Coev

variable (X Y)

/-- The coevaluation map `Y → C(X, Y × X)` sending a point `y : Y` to the continuous function
on `X` sending `y` to `(y, x)`. -/
def coev (y : Y) : C(X, Y × X) :=
  { toFun := Prod.mk y }
#align continuous_map.coev ContinuousMap.coev

variable {X Y}

theorem image_coev {y : Y} (s : Set X) : coev X Y y '' s = ({y} : Set Y) ×ˢ s := by
  aesop
#align continuous_map.image_coev ContinuousMap.image_coev

-- The coevaluation map Y → C(X, Y × X) is continuous (always).
theorem continuous_coev : Continuous (coev X Y) :=
  continuous_generateFrom <| by
    rintro _ ⟨s, sc, u, uo, rfl⟩
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (↑(coev X Y y) '' s ⊆ u) := hy
    -- porting notes: was below
    --change coev X Y y '' s ⊆ u at hy
    rw [image_coev s] at hy'
    rcases generalized_tube_lemma isCompact_singleton sc uo hy' with ⟨v, w, vo, _, yv, sw, vwu⟩
    refine' ⟨v, _, vo, singleton_subset_iff.mp yv⟩
    intro y' hy'
    change coev X Y y' '' s ⊆ u
    rw [image_coev s]
    exact (prod_mono (singleton_subset_iff.mpr hy') sw).trans vwu
#align continuous_map.continuous_coev ContinuousMap.continuous_coev

end Coev

section Curry

/-- Auxiliary definition, see `ContinuousMap.curry` and `Homeomorph.curry`. -/
def curry' (f : C(X × Y, Z)) (x : X) : C(Y, Z) :=
  ⟨Function.curry f x, Continuous.comp f.2 (continuous_const.prod_mk continuous_id)⟩
  -- Porting note: proof was `by continuity`
#align continuous_map.curry' ContinuousMap.curry'

/-- If a map `X × Y → Z` is continuous, then its curried form `X → C(Y, Z)` is continuous. -/
theorem continuous_curry' (f : C(X × Y, Z)) : Continuous (curry' f) :=
  have hf : curry' f = ContinuousMap.comp f ∘ coev _ _ := by ext; rfl
  hf ▸ Continuous.comp (continuous_comp f) continuous_coev
#align continuous_map.continuous_curry' ContinuousMap.continuous_curry'

/-- To show continuity of a map `X → C(Y, Z)`, it suffices to show that its uncurried form
    `X × Y → Z` is continuous. -/
theorem continuous_of_continuous_uncurry (f : X → C(Y, Z))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  continuous_curry' ⟨_, h⟩
#align continuous_map.continuous_of_continuous_uncurry ContinuousMap.continuous_of_continuous_uncurry

/-- The curried form of a continuous map `X × Y → Z` as a continuous map `X → C(Y, Z)`.
    If `x × Y` is locally compact, this is continuous. If `X` and `Y` are both locally
    compact, then this is a homeomorphism, see `Homeomorph.curry`. -/
def curry (f : C(X × Y, Z)) : C(X, C(Y, Z)) :=
  ⟨_, continuous_curry' f⟩
#align continuous_map.curry ContinuousMap.curry

@[simp]
theorem curry_apply (f : C(X × Y, Z)) (x : X) (y : Y) : f.curry x y = f (x, y) :=
  rfl
#align continuous_map.curry_apply ContinuousMap.curry_apply

/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (X × Y)] :
    Continuous (curry : C(X × Y, Z) → C(X, C(Y, Z))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval'
#align continuous_map.continuous_curry ContinuousMap.continuous_curry

/-- The uncurried form of a continuous map `X → C(Y, Z)` is a continuous map `X × Y → Z`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval'.comp <| f.continuous.prod_map continuous_id
#align continuous_map.continuous_uncurry_of_continuous ContinuousMap.continuous_uncurry_of_continuous

/-- The uncurried form of a continuous map `X → C(Y, Z)` as a continuous map `X × Y → Z` (if `Y` is
    locally compact). If `X` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `Homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace Y] (f : C(X, C(Y, Z))) : C(X × Y, Z) :=
  ⟨_, continuous_uncurry_of_continuous f⟩
#align continuous_map.uncurry ContinuousMap.uncurry

/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    Continuous (uncurry : C(X, C(Y, Z)) → C(X × Y, Z)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  apply continuous_eval'.comp (continuous_eval'.prod_map continuous_id)
#align continuous_map.continuous_uncurry ContinuousMap.continuous_uncurry

/-- The family of constant maps: `Y → C(X, Y)` as a continuous map. -/
def const' : C(Y, C(X, Y)) :=
  curry ContinuousMap.fst
#align continuous_map.const' ContinuousMap.const'

@[simp]
theorem coe_const' : (const' : Y → C(X, Y)) = const X :=
  rfl
#align continuous_map.coe_const' ContinuousMap.coe_const'

theorem continuous_const' : Continuous (const X : Y → C(X, Y)) :=
  const'.continuous
#align continuous_map.continuous_const' ContinuousMap.continuous_const'

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {X : Type*} {Y : Type*} {Z : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying as a homeomorphism between the function spaces `C(X × Y, Z)` and `C(X, C(Y, Z))`. -/
def curry [LocallyCompactSpace X] [LocallyCompactSpace Y] : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩
#align homeomorph.curry Homeomorph.curry

/-- If `X` has a single element, then `Y` is homeomorphic to `C(X, Y)`. -/
def continuousMapOfUnique [Unique X] : Y ≃ₜ C(X, Y) where
  toFun := const X
  invFun f := f default
  left_inv y := rfl
  right_inv f := by
    ext x
    rw [Unique.eq_default x]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _
#align homeomorph.continuous_map_of_unique Homeomorph.continuousMapOfUnique

@[simp]
theorem continuousMapOfUnique_apply [Unique X] (y : Y) (x : X) : continuousMapOfUnique y x = y :=
  rfl
#align homeomorph.continuous_map_of_unique_apply Homeomorph.continuousMapOfUnique_apply

@[simp]
theorem continuousMapOfUnique_symm_apply [Unique X] (f : C(X, Y)) :
    continuousMapOfUnique.symm f = f default :=
  rfl
#align homeomorph.continuous_map_of_unique_symm_apply Homeomorph.continuousMapOfUnique_symm_apply

end Homeomorph

section QuotientMap

variable {X₀ X Y Z : Type*} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ → X}

theorem QuotientMap.continuous_lift_prod_left (hf : QuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
#align quotient_map.continuous_lift_prod_left QuotientMap.continuous_lift_prod_left

theorem QuotientMap.continuous_lift_prod_right (hf : QuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap
#align quotient_map.continuous_lift_prod_right QuotientMap.continuous_lift_prod_right

end QuotientMap
