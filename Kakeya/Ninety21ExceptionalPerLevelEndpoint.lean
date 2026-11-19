module

public import Kakeya.Ninety21Theorem46Endpoint
public import Kakeya.Ninety21ActualAngularPackingEndpoint
public import Kakeya.Ninety21CompactGreedyPackingIntegration

/-!
# Exceptional packing and the per-level Theorem 4.6 endpoint

The regular incidence fibers count only original tube indices.  Exceptional
pieces are counted by Vitali packing at the same dyadic level.  The two bounds
combine before the dyadic moment summation.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Remaining-piece budget from regular original-tube fibers and exceptional
Vitali packing, at a fixed dyadic level. -/
theorem paper46_remaining_count_of_exceptional_budget
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (hFiberLower : ∀ r : {r : T //
      r ∈ paper46RegularIndices μ tubes n s m a},
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s m a ell = some r
          then (1 : ℝ) else 0)
    (Cexc : ℝ)
    (hExceptional :
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ tubes n s m).card : ℝ) ≤
          Cexc * (Fintype.card T : ℝ)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((s.P m).card : ℝ) ≤
        (1 + Cexc) * (Fintype.card T : ℝ) := by
  classical
  have hReg := paper46_regular_count_of_fibers μ tubes n s m a hFiberLower
  have hPart : ((s.P m).card : ℝ) =
      ((paperRegularPieces μ tubes n s m).card : ℝ) +
        ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
    exact_mod_cast (paper_regular_exceptional_card μ tubes n s m).symm
  rw [hPart]
  nlinarith

/-- The complete retained family consists of selected tubes and remaining
pieces.  Its per-level count uses no geometric auxiliary tubes. -/
theorem paper46_retained_count_of_exceptional_budget
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (hFiberLower : ∀ r : {r : T //
      r ∈ paper46RegularIndices μ tubes n s m a},
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s m a ell = some r
          then (1 : ℝ) else 0)
    (Cexc : ℝ)
    (hExceptional :
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ tubes n s m).card : ℝ) ≤
          Cexc * (Fintype.card T : ℝ)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
        (3 + Cexc) * (Fintype.card T : ℝ) := by
  have hRest := paper46_remaining_count_of_exceptional_budget
    μ tubes n s m a hFiberLower Cexc hExceptional
  have hSelected := s.hGreedy m
  nlinarith

/-- Construction and per-level exceptional packing data for large dyadic scales. -/
structure Paper46PerLevelInputs
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) where
  large : Paper46LargeLevelInputs μ tubes n s
  exceptionalConstant : ℝ
  hExceptionalNonneg : 0 ≤ exceptionalConstant
  hExceptional : ∀ (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (_hlarge : large.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m),
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s m).card : ℝ) ≤
        exceptionalConstant * (Fintype.card T : ℝ)

/-- Theorem 4.6's retained cardinality bound without a cross-level
exceptional overhead. -/
theorem paper46_large_level_retained_count_per_level
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (a : Paper46PerLevelInputs μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.large.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
        (3 + a.exceptionalConstant) * (Fintype.card T : ℝ) := by
  exact paper46_retained_count_of_exceptional_budget μ tubes n s m
    (a.large.construction m hlarge) (a.large.hFiberLower m hlarge)
    a.exceptionalConstant (a.hExceptional m hlarge)

/-- Analytic level estimate with the exceptional packing term counted at
this level only. -/
theorem paper46_analytic_level_budget_per_level
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46PerLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.large.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        (1 / (1 - Real.exp (-1))) * s.C *
          ((3 + a.exceptionalConstant) * s.Z) * s.radius m := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let H : ℝ := 1 / (1 - Real.exp (-1))
  let U : ℝ := (3 + a.exceptionalConstant) * (Fintype.card T : ℝ)
  let v : ℝ := s.C * s.deltaPow * s.radius m
  have hH : 0 ≤ H := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hv : 0 ≤ v :=
    mul_nonneg (mul_nonneg s.hC s.hDeltaPow) (s.hRadiusNonneg m)
  have hCount : q *
      ((Finset.univ : Finset
        ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m})).card : ℝ) ≤
        U := by
    have hc := paper46_large_level_retained_count_per_level μ tubes n s a m hlarge
    simpa [q, U, Fintype.card_sum] using hc
  have hVolume : ∀ p ∈ (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m})),
        Kakeya.Conditional.mass μ (s.retainedPiece m p) ≤ v := by
    intro p hp
    exact s.hVolume m p
  have hCapture : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * ∑ p, Kakeya.Conditional.mass μ (s.retainedPiece m p) := by
    have h := paper46_analytic_capture μ tubes n s c hT m
      (a.large.construction m hlarge)
    rw [paper46_analytic_mass_sum μ tubes n s m
      (a.large.construction m hlarge)] at h
    exact h
  have hBudget := localized_level_bound
    (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}))
    (fun p => Kakeya.Conditional.mass μ (s.retainedPiece m p))
    (Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m))
    H v q U 1 hH hv (Kakeya.Eighty4.dyadicScale_pos _ m).le
    hCapture hVolume (by simpa only [one_mul] using hCount)
  have hCoeff : 0 ≤ H * s.C * s.radius m :=
    mul_nonneg (mul_nonneg hH s.hC) (s.hRadiusNonneg m)
  have hFactor : 0 ≤ 3 + a.exceptionalConstant := by
    linarith [a.hExceptionalNonneg]
  have hNorm : (3 + a.exceptionalConstant) *
      ((Fintype.card T : ℝ) * s.deltaPow) ≤
        (3 + a.exceptionalConstant) * s.Z :=
    mul_le_mul_of_nonneg_left s.hNormalization hFactor
  change q * Kakeya.Conditional.mass μ
    (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * s.C * ((3 + a.exceptionalConstant) * s.Z) * s.radius m
  calc
    _ ≤ H * U * v := by simpa [U] using hBudget
    _ = (H * s.C * s.radius m) *
        ((3 + a.exceptionalConstant) *
          ((Fintype.card T : ℝ) * s.deltaPow)) := by
            dsimp [U, v]
            ring
    _ ≤ (H * s.C * s.radius m) *
        ((3 + a.exceptionalConstant) * s.Z) :=
      mul_le_mul_of_nonneg_left hNorm hCoeff
    _ = H * s.C * ((3 + a.exceptionalConstant) * s.Z) * s.radius m := by
      ring

/-- Uniform large-level moment contribution from the per-level count. -/
theorem paper46_large_uniform_level_budget_per_level
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46PerLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.large.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        (1 / (1 - Real.exp (-1))) * s.C *
          ((3 + a.exceptionalConstant) * s.Z) * s.radiusCap := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let alpha : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  let W : ℝ := (1 / (1 - Real.exp (-1))) * s.C *
    ((3 + a.exceptionalConstant) * s.Z)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ alpha := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + alpha) = q * q ^ alpha := by
    rw [Real.rpow_add hq 1 alpha, Real.rpow_one]
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hFactor : 0 ≤ 3 + a.exceptionalConstant := by
    linarith [a.hExceptionalNonneg]
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (mul_nonneg hH s.hC)
      (mul_nonneg hFactor hZ)
  have hLevel := paper46_analytic_level_budget_per_level μ tubes n s c a hT m hlarge
  have hScaled := mul_le_mul_of_nonneg_left hLevel hqa
  have hCap := mul_le_mul_of_nonneg_left (s.hRadiusScale m) hW
  change q ^ (1 + alpha) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        W * s.radiusCap
  calc
    _ = (q ^ alpha) *
        (q * Kakeya.Conditional.mass μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
            rw [hpow]
            ring
    _ ≤ (q ^ alpha) * (W * s.radius m) := by
      simpa only [W] using hScaled
    _ = W * (q ^ alpha * s.radius m) := by ring
    _ ≤ W * s.radiusCap := hCap

/-- The large-level constant and the finite small-level mass bound. -/
noncomputable def paper46PerLevelEndpointBudget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (cutoff Cexc : ℝ) : ℝ :=
  (1 / (1 - Real.exp (-1))) * s.C *
    ((3 + Cexc) * s.Z) * s.radiusCap +
    cutoff ^ (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ Set.univ

/-- All dyadic levels satisfy one moment budget, with exceptional packing
counted separately at each large scale. -/
theorem paper46_analytic_uniform_level_budget_per_level
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46PerLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        paper46PerLevelEndpointBudget μ tubes n s
          a.large.cutoff a.exceptionalConstant := by
  have hmass : 0 ≤ Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg _ x)
  have hsmallNonneg : 0 ≤ a.large.cutoff ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [a.large.hCutoff]) _) hmass
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hFactor : 0 ≤ 3 + a.exceptionalConstant := by
    linarith [a.hExceptionalNonneg]
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hCap : 0 ≤ s.radiusCap := by
    exact (mul_nonneg (Real.rpow_nonneg
      (Kakeya.Eighty4.dyadicScale_pos _ m).le _) (s.hRadiusNonneg m)).trans
        (s.hRadiusScale m)
  have hlargeNonneg : 0 ≤ (1 / (1 - Real.exp (-1))) * s.C *
      ((3 + a.exceptionalConstant) * s.Z) * s.radiusCap :=
    mul_nonneg (mul_nonneg (mul_nonneg hH s.hC)
      (mul_nonneg hFactor hZ)) hCap
  unfold paper46PerLevelEndpointBudget
  by_cases hlarge : a.large.cutoff ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  · exact (paper46_large_uniform_level_budget_per_level
      μ tubes n s c a hT m hlarge).trans
        (le_add_of_nonneg_right hsmallNonneg)
  · have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
      apply div_nonneg (by norm_num)
      linarith
    exact (paper46_small_level_budget μ tubes
      ((1 : ℝ) / ((n : ℝ) - 1)) ha hT m a.large.cutoff
      (lt_of_not_ge hlarge)).trans (le_add_of_nonneg_left hlargeNonneg)

/-- The manuscript's single-logarithm moment estimate. -/
theorem full_conditional_kakeya_moment_of_paper46_per_level
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46PerLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
        (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
          paper46PerLevelEndpointBudget μ tubes n s
            a.large.cutoff a.exceptionalConstant *
              ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg (by norm_num)
    linarith
  have h := Kakeya.Eighty9.logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1))
    (paper46PerLevelEndpointBudget μ tubes n s a.large.cutoff a.exceptionalConstant)
    ha hT (paper46_analytic_uniform_level_budget_per_level μ tubes n hn s c a hT)
  rw [(Kakeya.Conditional.dimension_exponents n hn).1] at h
  exact h

/-- Norm estimate obtained from the uniform per-level budget. -/
theorem full_conditional_kakeya_of_paper46_per_level
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46PerLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46PerLevelEndpointBudget μ tubes n s
          a.large.cutoff a.exceptionalConstant *
            ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
              (((n : ℝ) - 1) / (n : ℝ)) := by
  exact Kakeya.Eighty9.logarithmic_norm_from_level_budgets μ tubes n hn
    (paper46PerLevelEndpointBudget μ tubes n s
      a.large.cutoff a.exceptionalConstant) hT
    (paper46_analytic_uniform_level_budget_per_level μ tubes n hn s c a hT)

/-- For sufficiently many directions, taking the angular threshold equal to
separation and the population constant equal to the normalized count satisfies
both quantitative angular hypotheses. -/
theorem angular_packing_parameters_of_card_bound
    {k : ℕ} {S : Type*} [Fintype S]
    (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ (1 : ℝ) / 2)
    (hCard : (8 : ℝ) * (5 : ℝ) ^ (k + 1) ≤ (Fintype.card S : ℝ)) :
    ∃ θ c : ℝ,
      0 < θ ∧ θ ≤ 1 / 2 ∧ ε ≤ θ ∧
      8 * (5 : ℝ) ^ (k + 1) * θ ^ (k + 1) ≤ c ∧
      c ≤ (Fintype.card S : ℝ) * ε ^ (k + 1) := by
  refine ⟨ε, (Fintype.card S : ℝ) * ε ^ (k + 1),
    hε, hεHalf, le_refl ε, ?_, le_refl _⟩
  exact mul_le_mul_of_nonneg_right hCard (pow_nonneg hε.le (k + 1))

/-- Occupied Vitali parents belong to the original selected family. -/
theorem ConcreteGreedyVitaliCandidates.retained_parents_subset
    {Y S : Type*} [MeasurableSpace Y] [MetricSpace Y] [Fintype S]
    {tubes : S → Set Y} (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card S)) :
    d.retained.B m ⊆ g.B m := by
  intro r hr
  change r ∈ (g.withOccupiedVitaliPieces d.selected).B m at hr
  change r ∈ g.activeVitaliTubes d.selected m at hr
  exact (Finset.mem_filter.mp hr).1

/-- Canonical-radius angular packing supplies the per-level exceptional
component of the analytic endpoint, without a sum of exceptional budgets. -/
theorem ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions
    {k : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (μ : Measure (Kakeya.Space (k + 2)))
    (center direction : S → Kakeya.Space (k + 2))
    (δ θ ε c A : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2) d.retained)
    (hδ : 0 ≤ δ)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := S) (k + 2) A m)
    (hTotal : δ * (Fintype.card S : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hθ : 0 < θ) (hθHalf : θ ≤ 1 / 2)
    (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hSeparated : ∀ i j : S, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hSmall : 8 * (5 : ℝ) ^ (k + 1) * θ ^ (k + 1) ≤ c)
    (hPopulation : c ≤ (Fintype.card S : ℝ) * ε ^ (k + 1))
    (a : Paper46LargeLevelInputs μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData) :
    ∃ L : ℕ, Nonempty (Paper46PerLevelInputs μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData) := by
  have hParents : ∀ m r,
      r ∈ (d.retained.toBallLocalized μ (k + 2) b).B m → r ∈ g.B m := by
    intro m r hr
    change r ∈ d.retained.B m at hr
    exact ConcreteGreedyVitaliCandidates.retained_parents_subset g d m hr
  have hδR : ∀ m, δ ≤ d.radius m := by
    intro m
    rw [hRadius m]
    exact delta_le_canonicalGreedyVitaliRadius_of_total_scale
      k A δ hδ hTotal m
  obtain ⟨L, hL⟩ := d.exceptional_scaled_budget_of_unit_directions
    μ center direction δ θ ε c g b hθ hθHalf hε hεθ hUnit
    hSeparated hSmall hPopulation hParents
  refine ⟨L, ⟨{
    large := a
    exceptionalConstant := 8 * (L : ℝ)
    hExceptionalNonneg := by positivity
    hExceptional := ?_
  }⟩⟩
  intro m _hlarge
  exact hL m (hδR m)

/-- The per-level exceptional packing constructor with angular constants
chosen from the separation scale and direction count. -/
theorem ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions_card_bound
    {k : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    (μ : Measure (Kakeya.Space (k + 2)))
    (center direction : S → Kakeya.Space (k + 2))
    (δ ε A : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2) d.retained)
    (hδ : 0 ≤ δ)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := S) (k + 2) A m)
    (hTotal : δ * (Fintype.card S : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hCard : (8 : ℝ) * (5 : ℝ) ^ (k + 1) ≤ (Fintype.card S : ℝ))
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hSeparated : ∀ i j : S, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (a : Paper46LargeLevelInputs μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData) :
    ∃ L : ℕ, Nonempty (Paper46PerLevelInputs μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData) := by
  obtain ⟨θ, c, hθ, hθHalf, hεθ, hSmall, hPopulation⟩ :=
    angular_packing_parameters_of_card_bound
      (k := k) (S := S) ε hε hεHalf hCard
  exact ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions
    μ center direction δ θ ε c A g d b hδ hRadius hTotal
    hθ hθHalf hε hεθ hUnit hSeparated hSmall hPopulation a

end Kakeya.Ninety21
