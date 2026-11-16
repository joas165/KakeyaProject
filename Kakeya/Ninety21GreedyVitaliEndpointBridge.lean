module

public import Kakeya.Ninety21GreedyVitaliBounds

/-!
# Maximal-unused greedy bounds and the two-radius endpoint

The dyadic scale and selected-tube bounds follow from the index range and
maximal-unused selection. Canonical radii identify the finite-net radius with
the analytic radius. The original-tube incidence and tube-count normalization
remain explicit geometric inputs.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- Every dyadic scale of a nonempty finite tube family is at most its size. -/
theorem dyadicScale_le_card
    {T : Type*} [Fintype T] [Nonempty T]
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
      (Fintype.card T : ℝ) := by
  have hN : 0 < Fintype.card T := Fintype.card_pos
  have hm : m.val ≤ Nat.log 2 (Fintype.card T) := by
    have h := m.isLt
    change m.val < Nat.log 2 (Fintype.card T) + 1 at h
    omega
  have hpow : (2 : ℕ) ^ m.val ≤
      (2 : ℕ) ^ Nat.log 2 (Fintype.card T) :=
    Nat.pow_le_pow_right (by norm_num) hm
  have hlog : (2 : ℕ) ^ Nat.log 2 (Fintype.card T) ≤
      Fintype.card T :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hN)
  unfold Kakeya.Eighty4.dyadicScale
  exact_mod_cast hpow.trans hlog

/-- A selected family contained in the first maximal-unused choices has the
usual greedy cardinality bound. -/
theorem ConcreteTubeBallGeometry.selected_card_of_maximal_unused_subset
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (g : ConcreteTubeBallGeometry tubes)
    (hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ tubes m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
  calc
    (g.B m).card ≤ (maximalUnusedDyadicSelected μ tubes m).card :=
      Finset.card_le_card (hB m)
    _ = _ := maximalUnusedDyadicSelected_card μ tubes m

/-- All active tubes in the unpadded gain-net geometry are among the
original maximal-unused greedy choices. -/
theorem ConcreteTubeBallGeometry.active_maximal_unused_subset
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (C : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T), T → Finset X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
      (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes)
      C radius).B m ⊆ maximalUnusedDyadicSelected μ tubes m := by
  change activeGainNetTubes (maximalUnusedDyadicSelected μ tubes) C m ⊆
    maximalUnusedDyadicSelected μ tubes m
  exact Finset.filter_subset _ _

/-- Concrete bounds from maximal-unused selection and the canonical radius.
Only normalization and original-tube ball incidence are quantitative inputs. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z K : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z)
    (hIncidence : ∀ m r,
      (∑ i : Fin (g.ballCount m),
        if (g.ball m i ∩ Kakeya.unitTube (center r) (direction r) δ).Nonempty
          then (1 : ℝ) else 0) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) :
    ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained := by
  have hRadius' : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) := by
    intro m
    simpa only [canonicalGreedyVitaliRadius] using hRadius m
  have hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
    intro m
    exact ConcreteTubeBallGeometry.selected_card_of_maximal_unused_subset μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g hB m
  exact ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds
    μ center direction δ hδ g d hT hv hDom
    A C Z K hA hC hK hCgeom hRadius' hCenters
    (fun m => dyadicScale_le_card (T := T) m) hSelected hNorm hIncidence

/-- Feed the bounds constructed from the original maximal-unused selection
directly into the two-radius analytic endpoint. -/
noncomputable def ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclidean
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z K : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hCpiece : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hCtriple : 6 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hCanonical : ∀ m, g.chosen m = maximalUnusedDyadicChosen μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z)
    (hIncidence : ∀ m r,
      (∑ i : Fin (g.ballCount m),
        if (g.ball m i ∩ Kakeya.unitTube (center r) (direction r) δ).Nonempty
          then (1 : ℝ) else 0) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) :
    let b := ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused
      μ center direction δ hδ g d hT hv hDom A C Z K hA hC hK hCpiece
      hRadius hCenters hB hNorm hIncidence
    ConcreteTwoRadiusGreedy μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained b := by
  dsimp only
  let b := ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused
    μ center direction δ hδ g d hT hv hDom A C Z K hA hC hK hCpiece
    hRadius hCenters hB hNorm hIncidence
  have hRadius' : ∀ m, d.radius m = twoRadiusRadius d.retained b m := by
    intro m
    change d.radius m = b.A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)))
    rw [hRadius m]
    rfl
  have hDeltaPow : b.deltaPow = δ ^ (k + 1) := by
    rfl
  have hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C := by
    exact hCtriple
  exact ConcreteTwoRadiusGreedy.ofCanonicalVitaliEuclidean μ center direction
    δ hδ g d b (Fintype.card_pos) hCanonical hT hv hDom
    hRadius' hDeltaPow hCgeom

end Kakeya.Ninety21
