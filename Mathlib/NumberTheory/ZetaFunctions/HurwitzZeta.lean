/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.ZetaFunctions.AbstractFuncEq
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

noncomputable section

open Complex Filter Topology Asymptotics Real Set

section defs

variable (a b : ℝ)

/-- First form of the Hurwitz zeta kernel. -/
def hurwitzZetaKernelEven (x : ℝ) : ℂ :=
  cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x + b) (I * x)

lemma continuousOn_hurwitzZetaKernelEven :
    ContinuousOn (hurwitzZetaKernelEven a b) (Ioi 0) := by
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · exact Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)
  · have h := continuousAt_jacobiTheta₂ (a * I * x + b) (?_ : 0 < im (I * x))
    · suffices : ContinuousAt (fun u ↦ (a * I * u + b, I * u) : ℝ → ℂ × ℂ) x
      · exact ContinuousAt.comp (f := fun u : ℝ ↦ (a * I * u + b, I * u)) h this
      apply Continuous.continuousAt
      refine Continuous.comp (g := fun u ↦ (a * I * u + b, I * u)) ?_ continuous_ofReal
      rw [continuous_prod_mk]
      exact ⟨(continuous_mul_left _).add continuous_const, continuous_mul_left _⟩
    · rwa [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, ofReal_re]

lemma hurwitzZetaKernelEven_neg :
    hurwitzZetaKernelEven (-a) (-b) = hurwitzZetaKernelEven a b := by
  ext1 x
  simp only [hurwitzZetaKernelEven, ofReal_neg, neg_mul, ← neg_add, jacobiTheta₂_neg_left, neg_sq]

/-- Up to a factor of norm one, `hurwitzZetaKernelEven` only depends on `a` modulo `ℤ`. -/
lemma hurwitzZetaKernelEven_add_fst (x : ℝ) :
    hurwitzZetaKernelEven (a + 1) b x = cexp (-2 * π * I * b) * hurwitzZetaKernelEven a b x := by
  simp only [hurwitzZetaKernelEven]
  have : ↑(a + 1) * I * ↑x + ↑b = ↑a * I * ↑x + ↑b + I * ↑x := by { push_cast; ring }
  simp_rw [this, jacobiTheta₂_add_left' (a * I * x + b) (I * x), ← mul_assoc, ← Complex.exp_add,
    ofReal_add, ofReal_one]
  ring_nf
  rw [I_sq]
  ring_nf

/-- `hurwitzZetaKernelEven` only depends on `b` modulo `ℤ`. -/
lemma hurwitzZetaKernelEven_add_snd (x : ℝ) :
    hurwitzZetaKernelEven a (b + 1) x = hurwitzZetaKernelEven a b x := by
  simp only [hurwitzZetaKernelEven, ofReal_add, ofReal_one, ← add_assoc, jacobiTheta₂_add_left]

lemma hurwitzZetaKernelEven_functional_equation {x : ℝ} (hx : 0 < x) :
    hurwitzZetaKernelEven a b x = 1 / ↑(x ^ (1 / 2 : ℝ)) * cexp (-2 * π * I * a * b) *
    hurwitzZetaKernelEven (-b) a (1 / x) := by
  simp only [hurwitzZetaKernelEven]
  rw [jacobiTheta₂_functional_equation _ (by rwa [I_mul_im, ofReal_re])]
  rw [← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add,
    ← mul_assoc _ (cexp _), mul_assoc _ _ (cexp _), ← Complex.exp_add]
  congr 3
  · rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul, ofReal_cpow hx.le]
    simp only [one_div, ofReal_inv, ofReal_ofNat]
  · field_simp [hx.ne']
    ring_nf
    rw [(by simp : I ^ 3 = I ^ (2 + 1)), pow_succ, I_sq]
    ring_nf
  · field_simp [ofReal_ne_zero.mpr hx.ne']
    ring_nf
    rw [I_sq]
    ring_nf
  · field_simp [hx.ne']
    rw [← mul_assoc, I_mul_I, neg_one_mul]

end defs

section asymp

variable {a : ℝ}

/-- The series of term-wise norms of the Hurwitz zeta kernels is convergent, and is bounded
above by something which decays rapidly as `t → ∞`. -/
lemma zetaKernelEven_bound_nat (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ ↦ rexp (-π * (n + a) ^ 2 * t)) ∧
    ∑' n : ℕ, rexp (-π * (n + a) ^ 2 * t) ≤ rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)) := by
  let f (n : ℕ) : ℝ := rexp (-π * (n + a) ^ 2 * t)
  let g (n : ℕ) : ℝ := rexp (-π * (n + a ^ 2) * t)
  have hfg n : f n ≤ g n
  · rw [Real.exp_le_exp, mul_le_mul_right ht, mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos),
      ← sub_nonneg]
    have u : (n : ℝ) ≤ (n : ℝ) ^ 2
    · simpa only [← Nat.cast_pow, Nat.cast_le] using Nat.le_self_pow two_ne_zero _
    convert add_nonneg (sub_nonneg.mpr u) (by positivity : 0 ≤ 2 * n * a) using 1
    ring
  have hg_sum : HasSum g (rexp (-π * a ^ 2 * t) / (1 - rexp (-π * t)))
  · have h0 : rexp (-π * t) < 1
    · rw [exp_lt_one_iff, neg_mul, neg_lt_zero]
      exact mul_pos pi_pos ht
    have h1 := hasSum_geometric_of_lt_1 (exp_pos _).le h0
    convert h1.mul_left (rexp (-π * a ^ 2 * t)) using 1 with n
    ext1 n
    simp only [g]
    rw [mul_add, add_mul, Real.exp_add, mul_comm (rexp _), ← Real.exp_nat_mul]
    ring_nf
  have hf_sum : Summable f := hg_sum.summable.of_nonneg_of_le (fun _ ↦ (exp_pos _).le) hfg
  refine ⟨hf_sum, ?_⟩
  rw [← hg_sum.tsum_eq]
  exact tsum_le_tsum hfg hf_sum hg_sum.summable

lemma zetaKernelEven_bound_int (ha : a ∈ Icc 0 1) {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) ∧ ∑' n : ℤ, rexp (-π * (n + a) ^ 2 * t) ≤
    (rexp (-π * a ^ 2 * t) + rexp (-π * (1 - a) ^ 2 * t)) / (1 - rexp (-π * t)) := by
  have (n : ℕ) : rexp (-π * (Int.negSucc n + a) ^ 2 * t) = rexp (-π * (n + (1 - a)) ^ 2 * t)
  · rw [Int.cast_negSucc, ← neg_sq]
    push_cast
    ring_nf
  have hnp : Summable (fun n : ℕ ↦ rexp (-π * (Int.negSucc n + a) ^ 2 * t)) ∧ ∑' n : ℕ,
      rexp (-π * (Int.negSucc n + a) ^ 2 * t) ≤ rexp (-π * (1 - a) ^ 2 * t) / (1 - rexp (-π * t))
  · simpa only [this] using zetaKernelEven_bound_nat (sub_nonneg.mpr ha.2) ht
  have : HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) ((∑' n : ℕ, rexp (-π * (n + a) ^ 2 * t))
    + (∑' n : ℕ, rexp (-π * (Int.negSucc n + a) ^ 2 * t)))
  · convert HasSum.int_rec (zetaKernelEven_bound_nat ha.1 ht).1.hasSum hnp.1.hasSum with n
    rcases n with m | m <;> rfl
  refine ⟨this.summable, ?_⟩
  rw [add_div]
  exact (le_of_eq this.tsum_eq).trans (add_le_add (zetaKernelEven_bound_nat ha.1 ht).2 hnp.2)

lemma hasSum_int_hurwitzZetaKernelEven (ha : a ∈ Icc 0 1) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * b * n) * rexp (-π * (n + a) ^ 2 * t))
    (hurwitzZetaKernelEven a b t) := by
  have : Summable (fun n : ℤ ↦ cexp (2 * π * I * b * n) * rexp (-π * (n + a) ^ 2 * t))
  · apply Summable.of_norm
    convert (zetaKernelEven_bound_int ha ht).1 using 2 with n
    rw [norm_mul, norm_real, norm_of_nonneg (exp_pos _).le,
      (by { push_cast; ring } : 2 * π * I * b * n = ↑(2 * π * b * n) * I),
      Complex.norm_eq_abs, Complex.abs_exp, re_ofReal_mul, I_re, mul_zero, Real.exp_zero, one_mul]
  convert this.hasSum
  simp_rw [hurwitzZetaKernelEven, jacobiTheta₂, push_cast, ← tsum_mul_left, ← Complex.exp_add]
  congr 1 with n
  ring_nf
  rw [I_sq]
  ring_nf

lemma hasSum_nat_hurwitzZetaKernelEven (ha : a ∈ Icc 0 1) (b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ cexp (2 * π * I * b * (n + 1)) * rexp (-π * (n + 1 + a) ^ 2 * t) +
      cexp (-2 * π * I * b * (n + 1)) * rexp (-π * (n + 1 - a) ^ 2 * t))
      (hurwitzZetaKernelEven a b t - rexp (-π * a ^ 2 * t)) := by
  have := (hasSum_int_hurwitzZetaKernelEven ha b ht).sum_nat_of_sum_int
  rw [← hasSum_nat_add_iff' 1] at this
  convert this using 1
  · ext1 n
    push_cast
    ring_nf
  · simp_rw [Finset.sum_range_one, push_cast, neg_zero, mul_zero, zero_add, Complex.exp_zero,
      one_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub, sub_eq_add_neg]

/-- The function `hurwitzZetaKernelEven - L` has exponential decay at `+∞`, for suitable `L`. -/
lemma isBigO_atTop_hurwitzZetaKernelEven (ha : a ∈ Ico 0 1) (b : ℝ) :
    ∃ r : ℝ, 0 < r ∧ IsBigO atTop (fun x ↦ hurwitzZetaKernelEven a b x - (if a = 0 then 1 else 0))
    (fun x ↦ Real.exp (-r * x)) := by
  -- First some auxiliary statements, proved inline because they're too boring to be lemmas
  have aux1 {c d : ℝ} (hcd : c ≤ d) :
      (fun t : ℝ ↦ rexp (-π * d * t)) =O[atTop] (fun t : ℝ ↦ rexp (-π * c * t))
  · apply Eventually.isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    rwa [norm_of_nonneg (exp_pos _).le, exp_le_exp, mul_le_mul_right ht,
      mul_le_mul_left_of_neg (neg_lt_zero.mpr pi_pos)]
  have aux2 x (b' : ℝ) (n : ℤ) : ‖cexp (2 * ↑π * I * ↑b' * ↑n) *
    ↑(rexp (-π * (↑n + a) ^ 2 * x))‖ = rexp (-π * (↑n + a) ^ 2 * x)
  · simp_rw [norm_mul, norm_real, norm_of_nonneg (exp_pos _).le, Complex.norm_eq_abs,
      Complex.abs_exp, ← ofReal_int_cast, ← ofReal_ofNat, re_mul_ofReal, ← ofReal_mul,
      re_ofReal_mul, I_re, mul_zero, zero_mul, Real.exp_zero, one_mul]
  have aux3 : IsBigO atTop (fun t : ℝ ↦ (1 - rexp (-π * t))⁻¹) (fun _ ↦ (1 : ℝ))
  · refine isBigO_iff.mpr ⟨(1 - rexp (-π))⁻¹, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [norm_one, mul_one, norm_inv, inv_le_inv, norm_of_nonneg, sub_le_sub_iff_left]
    · rw [exp_le_exp, neg_mul, neg_le_neg_iff]
      exact le_mul_of_one_le_right pi_pos.le hx
    · rw [sub_nonneg, exp_le_one_iff, neg_mul, neg_nonpos]
      exact mul_nonneg pi_pos.le (zero_le_one.trans hx)
    · refine lt_of_lt_of_le ?_ (le_norm_self _)
      rw [sub_pos,  exp_lt_one_iff, neg_mul, neg_lt_zero]
      exact mul_pos pi_pos (zero_lt_one.trans_le hx)
    · rw [sub_pos, exp_lt_one_iff, neg_lt_zero]
      exact pi_pos
  -- now split into cases according to whether `a = 0` or not
  rcases lt_or_eq_of_le ha.1 with ha' | rfl
  · refine ⟨π * min (a ^ 2) ((1 - a) ^ 2),
      mul_pos pi_pos (lt_min_iff.mpr ⟨pow_pos ha' 2, pow_pos (by linarith [ha.2]) 2⟩), ?_⟩
    simp_rw [eq_false_intro ha'.ne', if_false, sub_zero]
    let h := fun t ↦ (rexp (-π * a ^ 2 * t) + rexp (-π * (1 - a) ^ 2 * t)) / (1 - rexp (-π * t))
    refine (?_ : IsBigO _ _ h).trans ?_ -- TODO: this should be "transitivity h"
    · apply Eventually.isBigO
      filter_upwards [eventually_gt_atTop 0] with x hx
      refine le_trans ?_ (zetaKernelEven_bound_int ⟨ha.1, ha.2.le⟩ hx).2
      rw [← (hasSum_int_hurwitzZetaKernelEven ⟨ha.1, ha.2.le⟩ _ hx).tsum_eq]
      refine (norm_tsum_le_tsum_norm ?_).trans <| le_of_eq <| congr_arg _ <| funext <| aux2 x b
      exact funext (aux2 x b) ▸ (zetaKernelEven_bound_int ⟨ha.1, ha.2.le⟩ hx).1
    · suffices : IsBigO atTop (fun t : ℝ ↦ (rexp (-π * a ^ 2 * t) + rexp (-π * (1 - a) ^ 2 * t)))
        (fun x ↦ rexp (-π * min (a ^ 2) ((1 - a) ^ 2) * x))
      · simpa only [neg_mul, mul_one] using this.mul aux3
      exact (aux1 (min_le_left _ _)).add (aux1 (min_le_right _ _))
  · -- now `a = 0` case: this is much more awkward since there is a nontrivial constant term
    simp_rw [add_zero] at aux2 -- statement simplifes as a = 0 now
    simp only [if_true]
    let h := fun t ↦ rexp (-π * t) / (1 - rexp (-π * t))
    refine ⟨π, pi_pos, (?_ : IsBigO _ _ h).trans (by simpa only [mul_one]
        using (isBigO_refl (fun t ↦ rexp (-π * t)) _).mul aux3)⟩
    refine isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with x hx
    -- `hasSum_nat_hurwitzZetaKernelEven` gives a formula for `hurwitzZetaKernelEven - 1` as a sum
    have hs := hasSum_nat_hurwitzZetaKernelEven (left_mem_Icc.mpr zero_le_one) b hx
    simp_rw [add_zero, sub_zero, zero_pow two_pos, mul_zero, zero_mul, Real.exp_zero,
      ofReal_one] at hs
    rw [← hs.tsum_eq, two_mul ‖_‖, tsum_add]
    · refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · refine (norm_tsum_le_tsum_norm ?_).trans ?_
        · convert (zetaKernelEven_bound_nat zero_le_one hx).1 with n
          simpa only [Int.cast_add, Int.cast_one, add_zero] using aux2 x b (n + 1)
        · convert (zetaKernelEven_bound_nat zero_le_one hx).2 using 1 with n
          · congr 1 with n
            simpa using aux2 x b (n + 1)
          · rw [one_pow, mul_one]
            apply norm_of_nonneg
            apply div_nonneg (exp_pos _).le
            rw [sub_nonneg, exp_le_one_iff, neg_mul, neg_nonpos]
            exact (mul_pos pi_pos hx).le
      · refine (norm_tsum_le_tsum_norm ?_).trans ?_
        · convert (zetaKernelEven_bound_nat zero_le_one hx).1 with n
          simpa using aux2 x (-b) (n + 1)
        · convert (zetaKernelEven_bound_nat zero_le_one hx).2 using 1 with n
          · congr 1 with n
            simpa using aux2 x (-b) (n + 1)
          · rw [one_pow, mul_one]
            apply norm_of_nonneg
            apply div_nonneg (exp_pos _).le
            rw [sub_nonneg, exp_le_one_iff, neg_mul, neg_nonpos]
            exact (mul_pos pi_pos hx).le
    · apply Summable.of_norm
      convert (zetaKernelEven_bound_nat zero_le_one hx).1 with n
      simpa using aux2 x b (n + 1)
    · apply Summable.of_norm
      convert (zetaKernelEven_bound_nat zero_le_one hx).1 with n
      simpa using aux2 x (-b) (n + 1)

lemma Real.Ico_induction (P : ℝ → Prop)
    (hP_iff_add : ∀ t, P t ↔ P (t + 1)) (hP_Ico : ∀ t, t ∈ Ico 0 1 → P t) : ∀ t, P t := by
  have h_int : ∀ (n : ℤ) (t : ℝ), P t ↔ P (t + n)
  · let q (n : ℤ) : Prop := ∀ t, P t ↔ P (t + n)
    intro n
    induction' n using Int.induction_on with i hi i hi
    · simp only [q, Int.cast_zero, add_zero, forall_const]
    · intro t
      simp only [Int.cast_add, Int.cast_ofNat, Int.cast_one, ← add_assoc]
      refine (hi t).trans (hP_iff_add (t + i))
    · intro t
      rw [hi, hP_iff_add (t + ↑(-↑i - 1 : ℤ))]
      push_cast
      ring_nf
  intro t
  rw [← Int.fract_add_floor t, ← h_int]
  exact hP_Ico _ ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩

/-- The function `hurwitzZetaKernelEven - L` has exponential decay at `+∞`, for suitable `L`. -/
lemma isBigO_atTop_hurwitzZetaKernelEven' :
    ∀ a b : ℝ, ∃ r : ℝ, 0 < r ∧ IsBigO atTop (fun x ↦ hurwitzZetaKernelEven a b x -
      (if Int.fract a = 0 then cexp (-2 * π * I * a * b) else 0)) (fun x ↦ Real.exp (-r * x)) := by
  apply Real.Ico_induction
  · intro a
    simp_rw [Int.fract_add_one, ofReal_add, ofReal_one, add_comm (a : ℂ) 1,
      mul_add, mul_one, add_mul, Complex.exp_add, hurwitzZetaKernelEven_add_fst]
    have (c : ℝ) := mul_ite (Int.fract a = 0) (cexp (-2 * π * I * c))
      (cexp (-2 * ↑π * I * a * c)) 0
    simp_rw [mul_zero] at this
    simp_rw [← this, ← mul_sub, isBigO_const_mul_left_iff (Complex.exp_ne_zero _)]
  · intro a ha b
    convert isBigO_atTop_hurwitzZetaKernelEven ha b using 6 with r x
    have : Int.fract a = a
    · exact Int.fract_eq_self.mpr ha
    rw [this]
    split_ifs with h
    · rw [h, ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
    · rfl

end asymp

section FEPair

def hurwitzFEPair (a b : ℝ) : WeakFEPair ℂ where
  hf_int := (continuousOn_hurwitzZetaKernelEven a b).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_hurwitzZetaKernelEven b (-a)).locallyIntegrableOn measurableSet_Ioi
  k := 1 / 2
  hk := by norm_num
  hε := Complex.exp_ne_zero (-2 * π * I * a * b)
  hf_top r :=
    let ⟨v, hv, hv'⟩ := isBigO_atTop_hurwitzZetaKernelEven' a b
    hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r :=
    let ⟨v, hv, hv'⟩ := isBigO_atTop_hurwitzZetaKernelEven' b (-a)
    hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by
    simp_rw [hurwitzZetaKernelEven_functional_equation b (-a) hx,
      smul_eq_mul, ofReal_neg, mul_neg, neg_mul, neg_neg, Complex.exp_neg]
    ring_nf
    field_simp [(rpow_pos_of_pos hx _).ne', Complex.exp_ne_zero]

end FEPair
