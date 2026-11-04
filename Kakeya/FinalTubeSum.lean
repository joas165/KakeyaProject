module
public import Mathlib
public import Kakeya.ConditionalKakeya

/-!
# Finite tube sums

Multiplicity, mass, and moment bounds for finite families of measurable tubes.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Eighty4

noncomputable def tubeMultiplicity {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) : ℝ :=
  ∑ i : T, Conditional.chi (tubes i) x

lemma tubeMultiplicity_nonneg {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) :
    0 ≤ tubeMultiplicity tubes x := by
  classical
  unfold tubeMultiplicity
  apply Finset.sum_nonneg
  intro i _
  by_cases hx : x ∈ tubes i <;> simp [Conditional.chi, Set.indicator, hx]

end Kakeya.Eighty4
