module
public import Mathlib

/-!
# Selection comparison

Finite incidence counts and comparison lemmas for selected families.
-/

@[expose] public section

open scoped BigOperators

namespace Kakeya.Seventy7

variable {P T : Type*} [Fintype P] [Fintype T]

noncomputable def weight (R : T → P → Prop) (c : P → ℝ) (j : T) : ℝ := by
  classical
  exact ∑ p, if R j p then c p else 0

noncomputable def degree (R : T → P → Prop) (A : Finset T) (p : P) : ℝ := by
  classical
  exact ∑ j ∈ A, if R j p then (1 : ℝ) else 0

theorem weighted_double_count (R : T → P → Prop) (c : P → ℝ)
    (A : Finset T) :
    (∑ j ∈ A, weight R c j) = ∑ p, degree R A p * c p := by
  classical
  unfold weight degree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

theorem degree_ge_one_of_covered (R : T → P → Prop) (A : Finset T)
    (p : P) (hcover : ∃ j ∈ A, R j p) : 1 ≤ degree R A p := by
  classical
  obtain ⟨j, hj, hR⟩ := hcover
  have h := Finset.single_le_sum
    (f := fun k : T => if R k p then (1 : ℝ) else 0)
    (fun k hk => by split_ifs <;> norm_num) hj
  simpa [degree, hR] using h

theorem incidence_double_count (R : T → P → Prop) (A : Finset T) :
    (∑ p, degree R A p) = ∑ j ∈ A, weight R (fun _ => 1) j := by
  simpa using (weighted_double_count R (fun _ => 1) A).symm

end Kakeya.Seventy7
