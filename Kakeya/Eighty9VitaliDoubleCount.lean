module
public import Mathlib
public import Kakeya.SelectionComparison

/-!
# Vitali incidence double counting

Weighted incidence identities for selected tubes and localized pieces.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Eighty9

section FiniteDoubleCount

variable {T P : Type*} [Fintype T] [Fintype P]

theorem selected_incidence_double_count
    (R : T → P → Prop) (B : Finset T)
    (hColumn : ∀ p : P, ∃ j ∈ B, R j p)
    (hRow : ∀ j ∈ B,
      Kakeya.Seventy7.weight R (fun _ => 1) j ≤ 1) :
    (Fintype.card P : ℝ) ≤ (B.card : ℝ) := by
  classical
  have hColumnDegree : ∀ p : P,
      (1 : ℝ) ≤ Kakeya.Seventy7.degree R B p := by
    intro p
    exact Kakeya.Seventy7.degree_ge_one_of_covered R B p (hColumn p)
  calc
    (Fintype.card P : ℝ) = ∑ _p : P, (1 : ℝ) := by simp
    _ ≤ ∑ p : P, Kakeya.Seventy7.degree R B p :=
      Finset.sum_le_sum (fun p _ => hColumnDegree p)
    _ = ∑ j ∈ B, Kakeya.Seventy7.weight R (fun _ => 1) j :=
      Kakeya.Seventy7.incidence_double_count R B
    _ ≤ ∑ _j ∈ B, (1 : ℝ) :=
      Finset.sum_le_sum (fun j hj => hRow j hj)
    _ = (B.card : ℝ) := by simp

end FiniteDoubleCount

end Kakeya.Eighty9
