/-
Copyright (c) 2024 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Div
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.GeomSum

#align_import data.nat.choose.basic from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"
#align_import data.polynomial.basic from "leanprover-community/mathlib"@"949dc57e616a621462062668c9f39e4e17b64b69"
#align_import data.polynomial.div from "leanprover-community/mathlib"@"e1e7190efdcefc925cb36f257a8362ef22944204"
#align_import data.polynomial.field_division from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"
#align_import field_theory.ratfunc from "leanprover-community/mathlib"@"bf9bbbcf0c1c1ead18280b0d010e417b10abb1b6"



/-!
# Gaussian Binomial Coefficients

This file defines Gaussian binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

## Tags

gaussian binomial coefficient
-/

noncomputable section

open Nat

namespace Nat

open Polynomial

open Finset BigOperators

-- polynomials? this should output a polynomial, not a nat

lemma degree_sum (n : ℕ) : degree (∑ i in range (n + 1), (X ^ i) : ℚ[X]) ≤ n := by
  induction' n with n hn
  · rw [range_one, sum_singleton]
    simp
  · rw [sum_range_succ]
    apply le_trans (degree_add_le (∑ x in range (n + 1), X ^ x : ℚ[X]) (X ^ (n + 1)))
      (max_le (le_trans hn (WithBot.coe_le_coe.2 (le_succ n)))
      (le_of_eq (@degree_X_pow ℚ _ _ (n + 1))))

/-- `q_factorial n` is the q-analog factorial of `n`. -/
def q_factorial : ℕ → ℚ[X]
  | 0 => 1
  | succ n => (∑ i in range (n + 1), (X ^ i)) * q_factorial n
#align nat.q_factorial Nat.q_factorial

@[simp] theorem q_factorial_zero : q_factorial 0 = 1 :=
  rfl
#align nat.q_factorial_zero Nat.q_factorial_zero

theorem q_factorial_succ (n : ℕ) : q_factorial (n + 1) =
  (∑ i in range (n + 1), (X ^ i)) * q_factorial n :=
  rfl
#align nat.q_factorial_succ Nat.q_factorial_succ

lemma q_factorial_Monic (n : ℕ) : Monic (q_factorial n) := by
  induction' n with n hn
  · rw [q_factorial_zero]
    simp
  · rw [q_factorial_succ]
    apply Monic.mul (@Polynomial.monic_geom_sum_X ℚ _ _ (succ_ne_zero n)) hn

@[simp] theorem q_factorial_ne_zero (k : ℕ) : q_factorial k ≠ 0 :=
  Monic.ne_zero (q_factorial_Monic k)

def gauss' (n k : ℕ) : RatFunc ℚ :=
  RatFunc.mk (q_factorial n) ((q_factorial k) * (q_factorial (n - k)))
#align nat.gauss' Nat.gauss'

@[simp]
theorem gauss'_zero_right (n : ℕ) : gauss' n 0 = 1 := by
  simp [gauss']
#align nat.gauss'_zero_right Nat.gauss'_zero_right

lemma RatFunc.mk_pow (p q : ℚ[X]) (n : ℕ) : (RatFunc.mk p q) ^ n = RatFunc.mk (p ^ n) (q ^ n) := by
  simp_all only [RatFunc.mk_eq_div, div_pow, map_pow]

lemma RatFunc.mk_add (p q r : ℚ[X]) :
  (RatFunc.mk p q) - (RatFunc.mk r q) = RatFunc.mk (p - r) (q) := by
  simp_all only [RatFunc.mk_eq_div, map_sub, div_eq_mul_inv, sub_mul]

lemma gauss'_succ (n k : ℕ) (hk : k ≤ n) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) : (gauss' (succ n) k) =
(RatFunc.mk (X ^ (n + 1) - 1) (X ^ (n + 1 - k) - 1)) * (gauss' n k) := by
  unfold gauss'
  simp [succ_sub hk, q_factorial_succ, RatFunc.mk_eq_div, map_mul (algebraMap ℚ[X] (RatFunc ℚ)),
    (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (n + 1), map_pow (algebraMap ℚ[X] (RatFunc ℚ)),
    RatFunc.algebraMap_X, @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ n),
    @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ (n - k))]
  rw [← mul_assoc, mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial k)),
    mul_assoc, ← map_mul (algebraMap ℚ[X] (RatFunc ℚ)), mul_div_mul_comm, div_div_div_eq,
    mul_comm _ (RatFunc.X - 1), mul_div_mul_comm, div_self (sub_ne_zero.2 h1), one_mul]

lemma gauss'_succ_succ (n k : ℕ) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) :
(gauss' (succ n) (succ k)) = (RatFunc.mk (X ^ (n + 1) - 1) (X ^ (k + 1) - 1)) * (gauss' n k) := by
  unfold gauss'
  simp [succ_sub_succ_eq_sub, q_factorial_succ, q_factorial_succ, RatFunc.mk_eq_div,
    map_mul (algebraMap ℚ[X] (RatFunc ℚ)), (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (n + 1),
    (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (k + 1), RatFunc.algebraMap_X,
    @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ n), @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ k)]
  rw [mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial k)), mul_assoc, mul_div_mul_comm,
    div_div_div_eq, mul_comm _ (RatFunc.X - 1), mul_div_mul_comm, div_self (sub_ne_zero.2 h1),
    one_mul, mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial (n - k))) _]

lemma gauss'_id (n k : ℕ) (hk : succ k ≤ n) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) :
gauss' n k = (RatFunc.mk (X ^ (k + 1) - 1) (X ^ (n - k) - 1)) * (gauss' n (succ k)) := by
  have h2 := gauss'_succ _ _ hk h1
  rw [gauss'_succ_succ n k h1, succ_sub_succ_eq_sub] at h2
  --rw [← @mul_left_cancel_iff _ _ _ (RatFunc.mk (X ^ (n + 1) - 1) (X ^ (k + 1) - 1)) _ _] at h2
  have h2 := @mul_cancel_left_coe_nonZeroDivisors (RatFunc ℚ) _
    (gauss' n k)
  --have h3 := nonZeroDivisors.ne_zero
  --have h4 :=
  sorry

@[simp]
theorem degree_gauss' (n k : ℕ) : RatFunc.intDegree (gauss' n k) = k • (n - k) := by sorry
#align nat.degree_gauss' Nat.degree_gauss'

theorem gauss'_recurrence (n k : ℕ) : (gauss' (succ n) (succ k)) =
  (algebraMap ℚ[X] (RatFunc ℚ) X ^ k) * (gauss' n (succ k)) + (gauss' n k) := by sorry

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. -/
def gauss : ℕ → ℕ → ℕ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gauss n k + X ^ k * gauss n (k + 1)
#align nat.gauss Nat.gauss

@[simp]
theorem gauss_zero_right (n : ℕ) : gauss n 0 = 1 := by cases n <;> rfl
#align nat.gauss_zero_right Nat.gauss_zero_right

@[simp]
theorem gauss_zero_succ (k : ℕ) : gauss 0 (succ k) = 0 :=
  rfl
#align nat.gauss_zero_succ Nat.gauss_zero_succ

theorem gauss_succ_succ (n k : ℕ) : gauss (succ n) (succ k) = gauss n k + X ^ k * gauss n (succ k) :=
  rfl
#align nat.gauss_succ_succ Nat.gauss_succ_succ

theorem gauss_eq_zero_of_lt : ∀ {n k}, n < k → gauss n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, k + 1, _ => gauss_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [gauss_succ_succ, gauss_eq_zero_of_lt hnk, gauss_eq_zero_of_lt hnk1, mul_zero, zero_add]
#align nat.gauss_eq_zero_of_lt Nat.gauss_eq_zero_of_lt

@[simp]
theorem gauss_self (n : ℕ) : gauss n n = 1 := by
  induction n <;> simp [*, gauss, gauss_eq_zero_of_lt (lt_succ_self _)]
#align nat.gauss_self Nat.gauss_self

@[simp]
theorem gauss_one_right (n : ℕ) : gauss n 1 = n := by induction n <;> simp [*, gauss, add_comm]
#align nat.gauss_one_right Nat.gauss_one_right

theorem gauss_eval₂_one_eq_choose (n k : ℕ) :
(gauss n k).eval₂ (RingHom.id ℕ) 1 = choose n k := by
  induction' k with k hk
  · sorry
  · induction' n with n hn
    · sorry
    · rw [gauss_succ_succ, choose_succ_succ, eval₂_add, eval₂_mul, eval₂_X_pow, one_pow, one_mul]
      sorry

  /-have : eval₂ (RingHom.id ℕ) 1 (gauss (succ n) (succ k)) = choose (succ n) (succ k) :=
    by
      · rw [gauss_succ_succ, choose_succ_succ, eval₂_add, eval₂_mul, eval₂_X_pow, one_pow, one_mul]
        sorry-/
  /-induction' n with n hn
  · sorry
  · induction' k with k hk
    · sorry
    · rw [gauss_succ_succ, choose_succ_succ, eval₂_add, eval₂_mul, eval₂_X_pow, one_pow, one_mul,
      hn]
      sorry-/
  /-induction n with
  | zero =>
    induction k with
    | zero =>
      rw [gauss_self, choose_self, eval₂_one]
    | succ n ih =>
      rw [gauss_zero_succ, choose_zero_succ, eval₂_zero]
  | succ n ihn =>
    induction k with
    | zero =>
      rw [gauss_zero_right, choose_zero_right, eval₂_one]
    | succ n ihk =>
      rw [gauss_succ_succ, choose_succ_succ, eval₂_add, eval₂_mul, eval₂_X_pow, one_pow, one_mul,
        ihn, ihk]-/

end Nat
