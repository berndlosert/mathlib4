/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Meromorphic functions
-/

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Meromorphy of `f` at `x` (more precisely, on a punctured neighbourhood of `x`; the value at
`x` itself is irrelevant). -/
def MeromorphicAt (f : 𝕜 → E) (x : 𝕜) :=
  ∃ (n : ℕ), AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x

lemma AnalyticAt.meromorphicAt {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x :=
  ⟨0, by simpa only [pow_zero, one_smul]⟩

lemma meromorphicAt_id (x : 𝕜) : MeromorphicAt id x := (analyticAt_id 𝕜 x).meromorphicAt

lemma meromorphicAt_const (e : E) (x : 𝕜) : MeromorphicAt (fun _ ↦ e) x :=
  analyticAt_const.meromorphicAt

namespace MeromorphicAt

lemma add {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨max m n, ?_⟩
  have : (fun z ↦ (z - x) ^ max m n • (f + g) z) = fun z ↦ (z - x) ^ (max m n - m) •
    ((z - x) ^ m • f z) + (z - x) ^ (max m n - n) • ((z - x) ^ n • g z)
  · simp_rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_max_left _ _),
      Nat.sub_add_cancel (Nat.le_max_right _ _), Pi.add_apply, smul_add]
  rw [this]
  exact ((((analyticAt_id 𝕜 x).sub analyticAt_const).pow _).smul hf).add
   ((((analyticAt_id 𝕜 x).sub analyticAt_const).pow _).smul hg)

lemma smul {f : 𝕜 → 𝕜} {g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f • g) x := by
  rcases hf with ⟨m, hf⟩
  rcases hg with ⟨n, hg⟩
  refine ⟨m + n, ?_⟩
  convert hf.smul hg using 2 with z
  rw [smul_eq_mul, ← mul_smul, mul_assoc, mul_comm (f z), ← mul_assoc, pow_add,
    ← smul_eq_mul (a' := f z), smul_assoc, Pi.smul_apply']

lemma mul {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x :=
  hf.smul hg

lemma neg {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (meromorphicAt_const (-1 : 𝕜) x).smul hf using 1
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]
lemma neg_iff {f : 𝕜 → E} {x : 𝕜} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

lemma sub {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg using 1
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
lemma congr {f g : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x := by
  rcases hf with ⟨m, hf⟩
  refine ⟨m + 1, ?_⟩
  have : AnalyticAt 𝕜 (fun z ↦ z - x) x := (analyticAt_id 𝕜 x).sub analyticAt_const
  refine (this.smul hf).congr ?_
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  filter_upwards [hfg] with z hz
  rcases eq_or_ne z x with rfl | hn
  · simp
  · rw [hz (Set.mem_compl_singleton_iff.mp hn), pow_succ, mul_smul]

lemma inv {f : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x := by
  rcases hf with ⟨m, hf⟩
  by_cases h_eq : (fun z ↦ (z - x) ^ m • f z) =ᶠ[𝓝 x] 0
  · -- silly case: f locally 0 near x
    apply (meromorphicAt_const 0 x).congr
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [h_eq] with z hfz hz
    rw [Pi.inv_apply, (smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)).mp hfz,
      inv_zero]
  · -- interesting case: use local formula for `f`
    obtain ⟨n, g, hg_an, hg_ne, hg_eq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h_eq
    have : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ (m + 1)) x :=
      ((analyticAt_id 𝕜 x).sub analyticAt_const).pow _
    -- use `m + 1` rather than `m` to damp out any silly issues with the value at `z = x`
    refine ⟨n + 1, (this.smul <| hg_an.inv hg_ne).congr ?_⟩
    filter_upwards [hg_eq, hg_an.continuousAt.eventually_ne hg_ne] with z hfg hg_ne'
    rcases eq_or_ne z x with rfl | hz_ne
    · simp only [sub_self, pow_succ, zero_mul, zero_smul]
    · simp_rw [smul_eq_mul] at hfg ⊢
      have aux1 : f z ≠ 0
      · have : (z - x) ^ n * g z ≠ 0 := mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz_ne)) hg_ne'
        rw [← hfg, mul_ne_zero_iff] at this
        exact this.2
      field_simp [sub_ne_zero.mpr hz_ne]
      rw [pow_succ, mul_assoc, hfg]
      ring

@[simp]
lemma inv_iff {f : 𝕜 → 𝕜} {x : 𝕜} :
    MeromorphicAt f⁻¹ x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, MeromorphicAt.inv⟩

lemma div {f g : 𝕜 → 𝕜} {x : 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  (div_eq_mul_inv f g).symm ▸ (hf.mul hg.inv)

/-- The order of vanishing of a meromorphic function, as an element of `ℤ ∪ ∞` (to include the
case of functions identically 0 near `x`). -/
noncomputable def order {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) : WithTop ℤ :=
  (hf.choose_spec.order.map (↑· : ℕ → ℤ)) - hf.choose

lemma order_eq_top_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) :
    hf.order = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  unfold order
  by_cases h : hf.choose_spec.order = ⊤
  · rw [h, WithTop.map_top, ← WithTop.coe_nat,
      WithTop.top_sub_coe, eq_self, true_iff, eventually_nhdsWithin_iff]
    rw [AnalyticAt.order_eq_top_iff] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← hm, WithTop.map_coe, WithTop.sub_eq_top_iff, eq_false_intro WithTop.coe_ne_top,
      false_and, false_iff, eventually_nhdsWithin_iff]
    contrapose! h
    rw [AnalyticAt.order_eq_top_iff]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff]
    filter_upwards [h] with z hfz hz
    rw [hfz hz, smul_zero]

lemma order_eq_int_iff {f : 𝕜 → E} {x : 𝕜} (hf : MeromorphicAt f x) (n : ℤ) : hf.order = n ↔
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  unfold order
  let p := hf.choose
  change hf.choose_spec.order.map (↑· : ℕ → ℤ) - ↑p = ↑n ↔
    ∃ g, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z = (z - x) ^ n • g z
  by_cases h : hf.choose_spec.order = ⊤
  · rw [h, WithTop.map_top, ← WithTop.coe_nat, WithTop.top_sub_coe,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [AnalyticAt.order_eq_top_iff] at h
    rintro ⟨g, hg_an, hg_ne, hg_eq⟩
    apply hg_ne
    apply Filter.EventuallyEq.eq_of_nhds
    rw [Filter.EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← h, WithTop.map_coe, ← WithTop.coe_nat, ← WithTop.coe_sub, WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (AnalyticAt.order_eq_nat_iff _ _).mp h.symm
    constructor
    · intro hmn
      refine hmn.symm ▸ ⟨g, hg_an, hg_ne, ?_⟩
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hfz hz
      rw [zpow_sub₀ (sub_ne_zero.mpr hz)]
      convert congr_arg (fun t ↦ (z - x) ^ (-↑(hf.choose) : ℤ) • t) hfz using 1
      · rw [← mul_smul, ← zpow_ofNat, ← zpow_add₀ (sub_ne_zero.mpr hz),
          neg_add_self, zpow_zero, one_smul]
      · rw [← mul_smul, ← zpow_ofNat, ← zpow_sub₀ (sub_ne_zero.mpr hz),
         ← zpow_add₀ (sub_ne_zero.mpr hz), sub_eq_neg_add (m : ℤ)]
    · rintro ⟨j, hj_an, hj_ne, hj_eq⟩
      -- Locally we have f z = (z - x) ^ n • j z, and
      -- (z - x) ^ p • f z = (z - x) ^ m • g z.
      -- So (z - x) ^ (p + n) • j z = (z - x) ^ m • g z.
      rw [eventually_nhdsWithin_iff] at hj_eq
      have := hg_eq.and hj_eq




  --   rw [eq_false_intro WithTop.top_ne_coe, false_iff]
  --   simp_rw [not_exists]
  --   intro g ⟨hg_an, hg_ne, hg_eq⟩
  --   apply hg_ne
  --   have hg_zero : ∃ᶠ z in 𝓝[≠] x, g z = 0
  --   · refine ((hg_eq.and h).mp ?_).frequently
  --     rw [eventually_nhdsWithin_iff]
  --     refine Filter.eventually_of_forall (fun z hz ⟨hz', hz''⟩ ↦ ?_)
  --     rwa [hz', smul_eq_zero_iff_right] at hz''
  --     exact zpow_ne_zero _ (sub_ne_zero.mpr <| by tauto)
  --   exact Filter.EventuallyEq.eq_of_nhds
  --     (hg_an.frequently_zero_iff_eventually_zero.mp hg_zero)
  -- · rw [WithTop.coe_inj, sub_eq_iff_eq_add]


end MeromorphicAt
