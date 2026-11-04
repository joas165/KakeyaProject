module
public import Mathlib
public import Kakeya.ConditionalKakeya
public import Kakeya.Eighty4DyadicLevels
public import Kakeya.FinalTubeSum

/-!
# Conditional multiplicity estimates

Finite tube multiplicity and moment bounds under explicit geometric hypotheses.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Eighty4

variable {X T : Type*} [MeasurableSpace X] [Fintype T] [DecidableEq T]

theorem tubeMultiplicity_le_card
    (tubes : T → Set X) (x : X) :
    tubeMultiplicity tubes x ≤ (Fintype.card T : ℝ) := by
  rw [tubeMultiplicity_eq_count]
  exact_mod_cast finiteTubeCount_le tubes x

theorem tubeMultiplicity_measurable
    (tubes : T → Set X)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    Measurable (tubeMultiplicity tubes) := by
  have hchi : ∀ i : T, Measurable (Kakeya.Conditional.chi (tubes i)) := by
    intro i
    exact measurable_const.indicator (hT i)
  unfold tubeMultiplicity
  exact Finset.measurable_sum _ (fun i _ => hchi i)

theorem tubeMoment_integrable
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (hT : ∀ i, MeasurableSet (tubes i))
    (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x => tubeMultiplicity tubes x ^ p) μ := by
  have hf : Measurable (fun x => tubeMultiplicity tubes x ^ p) :=
    (tubeMultiplicity_measurable tubes hT).pow_const p
  apply Integrable.of_bound hf.aestronglyMeasurable
    ((Fintype.card T : ℝ) ^ p)
  apply Filter.Eventually.of_forall
  intro x
  have hnonneg : 0 ≤ tubeMultiplicity tubes x :=
    tubeMultiplicity_nonneg tubes x
  have hpow : tubeMultiplicity tubes x ^ p ≤
      (Fintype.card T : ℝ) ^ p :=
    Real.rpow_le_rpow hnonneg (tubeMultiplicity_le_card tubes x) hp
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnonneg p)] using hpow

end Kakeya.Eighty4
