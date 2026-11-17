module

public import Kakeya.Ninety21GeometricPackingEndpoint

/-!
# Packing bounds for the compact maximal-unused greedy construction

The finite gain-net construction supplies the center, selected-tube, and
chosen-sequence identities used in the geometric Vitali packing bound.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- The compact maximal-unused gain nets give the dyadic centers and the
selected-tube and greedy-sequence identities. -/
theorem ConcreteGreedyVitaliCandidates.compactMaximalUnused_identifications
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) :
    let chosen := maximalUnusedDyadicChosen μ tubes
    let stage := maximalUnusedDyadicStage μ tubes
    let B := maximalUnusedDyadicSelected μ tubes
    let net := greedyFiniteNet tubes chosen stage radius hRadius hBound
    let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B chosen
      stage (maximalUnusedDyadic_hChosen μ tubes) net radius
    let d := ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
      μ tubes radius hRadius hBound
    (∀ m i, d.centers m i ∈ Kakeya.Eighty4.concreteDyadicBand tubes m) ∧
    (∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ tubes m) ∧
    (∀ m, g.chosen m = maximalUnusedDyadicChosen μ tubes m) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact ConcreteGreedyVitaliCandidates.ofCompactGreedyGains_centers_on_level
      tubes (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes)
      radius hRadius hBound (maximalUnusedDyadic_hStages μ tubes)
  · intro m
    exact ConcreteTubeBallGeometry.active_maximal_unused_subset μ tubes
      (greedyFiniteNet tubes (maximalUnusedDyadicChosen μ tubes)
        (maximalUnusedDyadicStage μ tubes) radius hRadius hBound) radius m
  · intro m
    rfl

/-- Concrete tube-ball bounds for the compact maximal-unused gain-net geometry.
The original tube centers remain arbitrary; only the directions are normalized. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanBoundsOfCompactMaximalUnusedGeometry
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ r, MeasurableSet (Kakeya.unitTube (center r) (direction r) δ))
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hTotalRadius : δ * (Fintype.card T : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand
        (fun r : T => Kakeya.unitTube (center r) (direction r) δ) m))
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z) :
    let tubes := fun r : T => Kakeya.unitTube (center r) (direction r) δ
    let radius := canonicalGreedyVitaliRadius (T := T) (k + 2) A
    let hRadius : ∀ m, 0 < radius m :=
      canonicalGreedyVitaliRadius_pos (T := T) (k + 2) A hA
    let net := greedyFiniteNet tubes (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes) radius hRadius hBound
    let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
      (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes) net radius
    let d := ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
      μ tubes radius hRadius hBound
    ConcreteTubeBallBounds μ tubes (k + 2) d.retained := by
  let tubes := fun r : T => Kakeya.unitTube (center r) (direction r) δ
  let radius := canonicalGreedyVitaliRadius (T := T) (k + 2) A
  have hRadius : ∀ m, 0 < radius m :=
    canonicalGreedyVitaliRadius_pos (T := T) (k + 2) A hA
  let net := greedyFiniteNet tubes (maximalUnusedDyadicChosen μ tubes)
    (maximalUnusedDyadicStage μ tubes) radius hRadius hBound
  let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
    (maximalUnusedDyadicSelected μ tubes)
    (maximalUnusedDyadicChosen μ tubes)
    (maximalUnusedDyadicStage μ tubes)
    (maximalUnusedDyadic_hChosen μ tubes) net radius
  let d := ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
    μ tubes radius hRadius hBound
  have hIdent := ConcreteGreedyVitaliCandidates.compactMaximalUnused_identifications
    μ tubes radius hRadius hBound
  have hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := hIdent.1
  have hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ tubes m :=
    hIdent.2.1
  have hRadiusEq : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m := by
    intro m
    rfl
  change ConcreteTubeBallBounds μ tubes (k + 2) d.retained
  exact d.euclideanBoundsOfMaximalUnusedGeometry
    μ center direction δ hδ g hT hUnit hDom A C Z hA hC hCgeom
    hRadiusEq hTotalRadius hCenters hB hNorm

/-- The concrete maximal-unused gain-net family satisfies the analytic
TwoRadiusGreedy endpoint with the derived parent-associated packing bound. -/
noncomputable def ConcreteTwoRadiusGreedy.ofCompactMaximalUnusedGeometry
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ r, MeasurableSet (Kakeya.unitTube (center r) (direction r) δ))
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCpiece : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hCtriple : 6 * tripleRadiusTransverseCoefficient k ≤ C)
    (hTotalRadius : δ * (Fintype.card T : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand
        (fun r : T => Kakeya.unitTube (center r) (direction r) δ) m))
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z) :
    let tubes := fun r : T => Kakeya.unitTube (center r) (direction r) δ
    let radius := canonicalGreedyVitaliRadius (T := T) (k + 2) A
    let hRadius : ∀ m, 0 < radius m :=
      canonicalGreedyVitaliRadius_pos (T := T) (k + 2) A hA
    let net := greedyFiniteNet tubes (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes) radius hRadius hBound
    let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
      (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes) net radius
    let d := ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
      μ tubes radius hRadius hBound
    let b := ConcreteGreedyVitaliCandidates.euclideanBoundsOfCompactMaximalUnusedGeometry
      μ center direction δ hδ hT hUnit hDom A C Z hA hC hCpiece
      hTotalRadius hBound hNorm
    ConcreteTwoRadiusGreedy μ tubes (k + 2) d.retained b := by
  let tubes := fun r : T => Kakeya.unitTube (center r) (direction r) δ
  let radius := canonicalGreedyVitaliRadius (T := T) (k + 2) A
  have hRadius : ∀ m, 0 < radius m :=
    canonicalGreedyVitaliRadius_pos (T := T) (k + 2) A hA
  let net := greedyFiniteNet tubes (maximalUnusedDyadicChosen μ tubes)
    (maximalUnusedDyadicStage μ tubes) radius hRadius hBound
  let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
    (maximalUnusedDyadicSelected μ tubes)
    (maximalUnusedDyadicChosen μ tubes)
    (maximalUnusedDyadicStage μ tubes)
    (maximalUnusedDyadic_hChosen μ tubes) net radius
  let d := ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
    μ tubes radius hRadius hBound
  have hIdent := ConcreteGreedyVitaliCandidates.compactMaximalUnused_identifications
    μ tubes radius hRadius hBound
  have hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := hIdent.1
  have hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ tubes m :=
    hIdent.2.1
  have hCanonical : ∀ m, g.chosen m = maximalUnusedDyadicChosen μ tubes m :=
    hIdent.2.2
  have hRadiusEq : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m := by
    intro m
    rfl
  change ConcreteTwoRadiusGreedy μ tubes (k + 2) d.retained
    (ConcreteGreedyVitaliCandidates.euclideanBoundsOfCompactMaximalUnusedGeometry
      μ center direction δ hδ hT hUnit hDom A C Z hA hC hCpiece
      hTotalRadius hBound hNorm)
  exact ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclideanGeometry
    μ center direction δ hδ g d hT hUnit hDom A C Z hA hC
    hCpiece hCtriple hRadiusEq hTotalRadius hCenters hB hCanonical hNorm

end Kakeya.Ninety21
