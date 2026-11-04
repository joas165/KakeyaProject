module
public import Mathlib
public import Kakeya.ConditionalKakeya
public import Kakeya.Eighty4ConditionalCompletion
public import Kakeya.Eighty4DyadicLevels
public import Kakeya.FinalTubeSum

/-!
# Logarithmic dyadic summation

Combines dyadic level budgets into logarithmic moment and norm estimates.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Eighty9

variable {X T : Type*} [MeasurableSpace X]

variable [Fintype T] [DecidableEq T]

theorem logarithmic_moment_from_level_budgets
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (a H : ℝ) (ha : 0 ≤ a)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hLevel : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^ (1 + a) *
        Kakeya.Conditional.mass μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤ H) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^ (1 + a) ∂μ) ≤
      (2 : ℝ) ^ (1 + a) * H *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  have hInt : Integrable
      (fun x => Kakeya.Eighty4.tubeMultiplicity tubes x ^ (1 + a)) μ :=
    Kakeya.Eighty4.tubeMoment_integrable μ tubes hT (1 + a) (by linarith)
  have hMoment := Kakeya.Conditional.moment_from_level_budgets μ
    (Kakeya.Eighty4.tubeMultiplicity tubes)
    (Kakeya.Eighty4.concreteDyadicBand tubes)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T))
    (1 + a) H
    (by linarith)
    (Kakeya.Eighty4.tubeMultiplicity_nonneg tubes)
    hInt
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT)
    (Kakeya.Eighty4.dyadicScale_pos (Fintype.card T))
    (Kakeya.Eighty4.concreteDyadicBand_condition tubes)
    hLevel
  simpa only [Kakeya.Eighty4.dyadicIndex_card] using hMoment

theorem logarithmic_norm_from_level_budgets
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n) (H : ℝ)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hLevel : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
        Kakeya.Conditional.mass μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤ H) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
          ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^
          (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) * H *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg
    · norm_num
    · linarith
  have hMoment := logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1)) H ha hT hLevel
  obtain ⟨he, hr⟩ := Kakeya.Conditional.dimension_exponents n hn
  rw [he] at hMoment
  have hRoot := Kakeya.Conditional.norm_of_moment_bound μ
    (Kakeya.Eighty4.tubeMultiplicity tubes)
    ((n : ℝ) / ((n : ℝ) - 1))
    ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) * H *
      ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ))
    (div_pos (by linarith) (by linarith)) hMoment
    (Kakeya.Eighty4.tubeMultiplicity_nonneg tubes)
  rw [he] at hr
  rw [hr] at hRoot
  exact hRoot

end Kakeya.Eighty9
