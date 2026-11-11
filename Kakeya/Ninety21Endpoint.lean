module
public import Kakeya.Ninety21CountingBridge
public import Kakeya.Eighty9DyadicSummation
public import Kakeya.Eighty9GreedyCover

/-!
# Conditional endpoint with one mass sum over retained pieces

The Hall sum type is used only for relabeling. All analytic masses are
measures of the actual retained sets `piece m l`, indexed by `l ∈ D m`.
The numerical input `hTubeCount` bounds *distinct tube indices* in `D m`.
It may be supplied by the repository's `scaled_tube_count` theorem, when
its genuine column and selected-index-budget premises hold. It cannot be
deduced from disjointness of trimmed pieces with repeated parent labels.
`inputs_of_greedy_cover` discharges capture using the existing greedy theorem.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Kakeya.Ninety21
variable {X T K : Type*} [MeasurableSpace X]
variable [Fintype T]

/-- Inputs at every actual dyadic level, including small q. Pieces may vary
with the level. The equivalence is supplied, not constructed in this module. -/
structure SelectedIncidenceDyadicData
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) where
  B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T
  P : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset K
  D : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T
  e : ∀ m, ({r : T // r ∈ B m} ⊕ {p : K // p ∈ P m}) ≃ {r : T // r ∈ D m}
  piece : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → Set X
  radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ
  C : ℝ
  deltaPow : ℝ
  Z : ℝ
  radiusCap : ℝ
  hC : 0 ≤ C
  hDeltaPow : 0 ≤ deltaPow
  hRadiusNonneg : ∀ m, 0 ≤ radius m
  hGreedy : ∀ m, Kakeya.Eighty4.dyadicScale (Fintype.card T) m * (B m).card ≤
    2 * (Fintype.card T : ℝ)
  hTubeCount : ∀ m,
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m * (D m).card ≤
      4 * (Fintype.card T : ℝ)
  hPieceVolume : ∀ m, ∀ l ∈ D m,
    Kakeya.Conditional.mass μ (piece m l) ≤ C * deltaPow * radius m
  hNormalization : (Fintype.card T : ℝ) * deltaPow ≤ Z
  hRadiusScale : ∀ m,
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      ((1 : ℝ) / ((n : ℝ) - 1)) * radius m ≤ radiusCap

/-- Low-level endpoint inputs. Capture is one sum over the full retained
piece family; there is no additional selected-object mass. -/
structure SelectedIncidenceDyadicInputs
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    extends SelectedIncidenceDyadicData (K := K) μ tubes n where
  H : ℝ
  hH : 0 ≤ H
  hCapture : ∀ m,
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * ∑ l ∈ D m, Kakeya.Conditional.mass μ (piece m l)

/-- The upstream premises of the existing greedy capture theorem, applied
to the SAME retained pieces as the count and volume bounds. -/
structure GreedyCaptureAtLevels
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (d : SelectedIncidenceDyadicData (K := K) μ tubes n) where
  Q : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → Set X
  hScaleLe : ∀ m, Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
    (Fintype.card T : ℝ)
  hUnionMeasurable : ∀ m, MeasurableSet (Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
  hUnionSubset : ∀ m, Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      Kakeya.Eighty4.concreteDyadicBand tubes m
  hStep : ∀ m k,
    Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (Q m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m / (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (Q m) k
  hPieceMeasurable : ∀ m, ∀ l ∈ d.D m, MeasurableSet (d.piece m l)
  hCover : ∀ m, Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ l ∈ d.D m, d.piece m l

/-- Reuse greedy capture, with the trimming already incorporated into each
retained set. This proves the endpoint's single-sum capture inequality. -/
theorem piece_mass_capture_of_greedy_cover
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (d : SelectedIncidenceDyadicData (K := K) μ tubes n)
    (c : GreedyCaptureAtLevels μ tubes n d)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) *
        ∑ l ∈ d.D m, Kakeya.Conditional.mass μ (d.piece m l) := by
  classical
  have h := Kakeya.Eighty4.mass_capture_from_greedy_union
    μ (Kakeya.Eighty4.concreteDyadicBand tubes m) (c.Q m)
    (d.piece m) (fun _ => Set.univ) (d.D m)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) (c.hScaleLe m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m)
    (c.hUnionMeasurable m) (c.hUnionSubset m) (c.hStep m)
    (by simpa using c.hPieceMeasurable m)
    (by simpa using c.hCover m)
  simpa using h

/-- Construct endpoint inputs with capture PROVED by greedy selection.
No `hCapture` argument is required. -/
noncomputable def inputs_of_greedy_cover
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (d : SelectedIncidenceDyadicData (K := K) μ tubes n)
    (c : GreedyCaptureAtLevels μ tubes n d)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    SelectedIncidenceDyadicInputs (K := K) μ tubes n where
  toSelectedIncidenceDyadicData := d
  H := 1 / (1 - Real.exp (-1))
  hH := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  hCapture := piece_mass_capture_of_greedy_cover μ tubes n d c hT

/-- Derive the level budget from the *distinct tube-index* budget and
single-sum greedy capture. Hall's bijection only transports piece masses. -/
theorem dyadic_level_budget_of_selected_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : SelectedIncidenceDyadicInputs (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        4 * g.H * g.C * g.Z * g.radius m := by
  classical
  have hV : 0 ≤ g.C * g.deltaPow * g.radius m :=
    mul_nonneg (mul_nonneg g.hC g.hDeltaPow) (g.hRadiusNonneg m)
  have hCount := g.hTubeCount m
  have hBound := localized_level_bound (g.D m)
    (fun l => Kakeya.Conditional.mass μ (g.piece m l))
    (Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m))
    g.H (g.C * g.deltaPow * g.radius m)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ) 4
    g.hH hV (Kakeya.Eighty4.dyadicScale_pos _ m).le
    (g.hCapture m) (g.hPieceVolume m) hCount
  have hCoef : 0 ≤ 4 * g.H * g.C * g.radius m :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) g.hH) g.hC) (g.hRadiusNonneg m)
  calc
    _ ≤ 4 * g.H * (Fintype.card T : ℝ) * (g.C * g.deltaPow * g.radius m) := hBound
    _ = (4 * g.H * g.C * g.radius m) * ((Fintype.card T : ℝ) * g.deltaPow) := by ring
    _ ≤ (4 * g.H * g.C * g.radius m) * g.Z :=
      mul_le_mul_of_nonneg_left g.hNormalization hCoef
    _ = 4 * g.H * g.C * g.Z * g.radius m := by ring

/-- Uniform budget with the constant 4 from the distinct tube-index count. -/
theorem uniform_level_budget_of_selected_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : SelectedIncidenceDyadicInputs (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      4 * g.H * g.C * g.Z * g.radiusCap := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let a : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ a := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + a) = q * q ^ a := by
    rw [Real.rpow_add hq 1 a, Real.rpow_one]
  have hBudget : q *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      4 * g.H * g.C * g.Z * g.radius m :=
    dyadic_level_budget_of_selected_incidence μ tubes n g m
  have hScaled := mul_le_mul_of_nonneg_left hBudget hqa
  have hCoef : 0 ≤ 4 * g.H * g.C * g.Z := by
    have hZ : 0 ≤ g.Z :=
      (mul_nonneg (Nat.cast_nonneg _) g.hDeltaPow).trans g.hNormalization
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) g.hH) g.hC) hZ
  have hCap := mul_le_mul_of_nonneg_left (g.hRadiusScale m) hCoef
  change q ^ (1 + a) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      4 * g.H * g.C * g.Z * g.radiusCap
  calc
    q ^ (1 + a) *
        Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) =
        (q ^ a) * (q *
          Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
      rw [hpow]
      ring
    _ ≤ (q ^ a) * (4 * g.H * g.C * g.Z * g.radius m) := hScaled
    _ = (4 * g.H * g.C * g.Z) * (q ^ a * g.radius m) := by ring
    _ ≤ (4 * g.H * g.C * g.Z) * g.radiusCap := hCap
    _ = 4 * g.H * g.C * g.Z * g.radiusCap := by ring

/-- Conditional logarithmic moment estimate from the Ninety21 bridge. -/
theorem full_conditional_kakeya_moment_of_selected_incidence
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : SelectedIncidenceDyadicInputs (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * g.H * g.C * g.Z * g.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg
    · norm_num
    · linarith
  have h := Kakeya.Eighty9.logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1)) (4 * g.H * g.C * g.Z * g.radiusCap) ha hT
    (uniform_level_budget_of_selected_incidence μ tubes n g)
  rw [(Kakeya.Conditional.dimension_exponents n hn).1] at h
  exact h

/-- Conditional endpoint: the remaining inputs are explicit in the structure. -/
theorem full_conditional_kakeya_of_selected_incidence
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : SelectedIncidenceDyadicInputs (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * g.H * g.C * g.Z * g.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  classical
  exact Kakeya.Eighty9.logarithmic_norm_from_level_budgets μ tubes n hn
    (4 * g.H * g.C * g.Z * g.radiusCap) hT
    (uniform_level_budget_of_selected_incidence μ tubes n g)

/-- Endpoint with capture discharged by the existing greedy theorem. -/
theorem full_conditional_kakeya_moment_of_greedy_cover
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (d : SelectedIncidenceDyadicData (K := K) μ tubes n)
    (c : GreedyCaptureAtLevels μ tubes n d)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * (1 / (1 - Real.exp (-1))) * d.C * d.Z * d.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  exact full_conditional_kakeya_moment_of_selected_incidence μ tubes n hn
    (inputs_of_greedy_cover μ tubes n d c hT) hT

/-- Endpoint with capture discharged by the existing greedy theorem. -/
theorem full_conditional_kakeya_of_greedy_cover
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (d : SelectedIncidenceDyadicData (K := K) μ tubes n)
    (c : GreedyCaptureAtLevels μ tubes n d)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * (1 / (1 - Real.exp (-1))) * d.C * d.Z * d.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  exact full_conditional_kakeya_of_selected_incidence μ tubes n hn
    (inputs_of_greedy_cover μ tubes n d c hT) hT

end Kakeya.Ninety21
