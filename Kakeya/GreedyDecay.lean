module
public import Mathlib

/-! Numerical part of Theorem 4.1: maximal-weight averaging, one-step decay,
iteration, exponential decay, and the ceiling budget. The construction of
the measurable greedy family remains a separate geometric task. -/

@[expose] public section

open scoped BigOperators
namespace Kakeya.Eighty4

theorem exists_greedy_average {T : Type*} [Fintype T] [Nonempty T]
    (w : T → ℝ) (q V : ℝ) (hmass : q * V ≤ ∑ i, w i) :
    ∃ j, (∀ i, w i ≤ w j) ∧ q * V ≤ (Fintype.card T : ℝ) * w j := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  refine ⟨j, fun i => hj i (Finset.mem_univ i), ?_⟩
  calc
    q * V ≤ ∑ i, w i := hmass
    _ ≤ ∑ _i : T, w j := Finset.sum_le_sum (fun i _ => hj i (Finset.mem_univ i))
    _ = (Fintype.card T : ℝ) * w j := by simp

theorem greedy_step_of_average (N q V Q Vnext : ℝ) (hN : 0 < N)
    (haverage : q * V ≤ N * Q) (hremove : Vnext = V - Q) :
    Vnext ≤ (1 - q / N) * V := by
  have hgain : (q / N) * V ≤ Q := by
    have h : q * V / N ≤ Q := (div_le_iff₀ hN).mpr (by nlinarith)
    convert h using 1 <;> ring
  rw [hremove]
  nlinarith

theorem greedy_remainder_bound (R : ℕ → ℝ) (t : ℝ)
    (ht : t ≤ 1) (hstep : ∀ k, R (k + 1) ≤ (1 - t) * R k) (k : ℕ) :
    R k ≤ (1 - t) ^ k * R 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      R (k + 1) ≤ (1 - t) * R k := hstep k
      _ ≤ (1 - t) * ((1 - t) ^ k * R 0) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - t) ^ (k + 1) * R 0 := by ring

theorem greedy_remainder_exp (R : ℕ → ℝ) (t : ℝ)
    (hR : 0 ≤ R 0) (ht : t ≤ 1)
    (hstep : ∀ k, R (k + 1) ≤ (1 - t) * R k) (k : ℕ) :
    R k ≤ Real.exp (-(k : ℝ) * t) * R 0 := by
  have he : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith
  calc
    R k ≤ (1 - t) ^ k * R 0 := greedy_remainder_bound R t ht hstep k
    _ ≤ (Real.exp (-t)) ^ k * R 0 := by
      apply mul_le_mul_of_nonneg_right _ hR
      exact pow_le_pow_left₀ (by linarith) he k
    _ = Real.exp (-(k : ℝ) * t) * R 0 := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

theorem greedy_major_portion (R : ℕ → ℝ) (t : ℝ) (K : ℕ)
    (hR : 0 ≤ R 0) (ht : t ≤ 1)
    (hstep : ∀ k, R (k + 1) ≤ (1 - t) * R k)
    (hK : 1 ≤ (K : ℝ) * t) :
    (1 - Real.exp (-1)) * R 0 ≤ R 0 - R K := by
  have hexp : Real.exp (-(K : ℝ) * t) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h := (greedy_remainder_exp R t hR ht hstep K).trans
    (mul_le_mul_of_nonneg_right hexp hR)
  nlinarith

theorem greedy_ceiling_budget (q N : ℝ) (hq : 0 < q) (hqN : q ≤ N) :
    N ≤ q * (⌈N / q⌉₊ : ℝ) ∧ q * (⌈N / q⌉₊ : ℝ) ≤ 2 * N := by
  have hN : 0 ≤ N := hq.le.trans hqN
  have hlo := Nat.le_ceil (N / q)
  have hhi := Nat.ceil_lt_add_one (div_nonneg hN hq.le)
  have hlo' := mul_le_mul_of_nonneg_left hlo hq.le
  have hhi' := mul_le_mul_of_nonneg_left hhi.le hq.le
  have hcancel : q * (N / q) = N := by field_simp
  constructor
  · simpa only [hcancel] using hlo'
  · rw [mul_add, hcancel, mul_one] at hhi'
    linarith

theorem greedy_capture_from_recurrence (R : ℕ → ℝ) (q N : ℝ)
    (hq : 0 < q) (hqN : q ≤ N) (hR : 0 ≤ R 0)
    (hstep : ∀ k, R (k + 1) ≤ (1 - q / N) * R k) :
    q * (⌈N / q⌉₊ : ℝ) ≤ 2 * N ∧
      R 0 ≤ (1 / (1 - Real.exp (-1))) * (R 0 - R ⌈N / q⌉₊) := by
  have hN : 0 < N := hq.trans_le hqN
  have hb := greedy_ceiling_budget q N hq hqN
  have ht : q / N ≤ 1 := (div_le_one hN).mpr hqN
  have hK : 1 ≤ (⌈N / q⌉₊ : ℝ) * (q / N) := by
    have h := (one_le_div hN).mpr hb.1
    simpa only [mul_div_assoc, mul_comm q] using h
  have hmass := greedy_major_portion R (q / N) ⌈N / q⌉₊ hR ht hstep hK
  have hpos : 0 < 1 - Real.exp (-1) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  refine ⟨hb.2, ?_⟩
  have h := (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmass)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h
end Kakeya.Eighty4
