module
public import Mathlib
public import Kakeya.Eighty9LowerIncidenceOnlyCompletion
public import Kakeya.Eighty9DyadicSummation

/-!
# Conditional Kakeya endpoint from lower incidences and the same-ball row bound

This module joins the two existing endpoints in the *reduced* user project:

* `reindexed_level_of_lower_incidence`: lower incidence + disjointness +
  pre-existing geometric inputs => q times dyadic level mass bound;
* `logarithmic_norm_from_level_budgets`: all dyadic level bounds =>
  the logarithmic Kakeya endpoint moment/norm estimate.

For the bijective map `k = e.symm` from all tube–ball labels to the
reindexed pieces, coverage of `Set.range E` is proved (not assumed).
Injectivity of E and nonemptiness give LowerIncidence E k.  This
full-label result is distinct from `LowerIncidenceAtLevels`, whose
representatives are indexed by selected tubes B; the latter is retained
as an explicit conditional input to the cardinality/endpoint argument.

The last part treats the manuscript's same-ball incidence.  Its row bound
`SameBallRowBoundAtLevels` is a visible `def`; it is PROVED by disjointness from
the equally visible assumption `SameBallIsRepresentativeAtLevels` (the test
piece of a selected tube is the piece of one fixed chosen label).  Without that
assumption the row of `r` is `|S m r|`, and the bound is the lower-incidence
content in another form.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Eighty9

variable {X T I K : Type*}
variable [MetricSpace X] [MeasurableSpace X]
variable [Fintype T] [DecidableEq T] [DecidableEq I] [DecidableEq K]

/-- All geometric and selection data across the *actual* dyadic levels of
`tubeMultiplicity tubes`. This groups the existing conditional geometric
hypotheses without introducing an additional assumed dyadic budget. -/
structure LocalizedDyadicInputs (μ : Measure X) (tubes : T → Set X) (n : ℕ) where
  B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T
  S : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → Finset I
  D : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset K
  e : ∀ m, {k : K // k ∈ D m} ≃ TubeWiseVitaliLabel (B m) (S m)
  gain : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → Set X
  centers : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → I → X
  radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ
  pieceMass : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → K → ℝ
  H : ℝ
  C : ℝ
  deltaPow : ℝ
  Z : ℝ
  radiusCap : ℝ
  hH : 0 ≤ H
  hC : 0 ≤ C
  hRadiusNonneg : ∀ m, 0 ≤ radius m
  hDeltaPow : 0 ≤ deltaPow
  hNonemptyFiber : ∀ m, ∀ j ∈ B m, (S m j).Nonempty
  hGain : ∀ m, ∀ j ∈ B m, ∀ j' ∈ B m,
    j ≠ j' → Disjoint (gain m j) (gain m j')
  hBalls : ∀ m, ∀ j ∈ B m, ∀ i ∈ S m j, ∀ i' ∈ S m j,
    i ≠ i' → Disjoint (Metric.ball (centers m j i) (radius m))
      (Metric.ball (centers m j i') (radius m))
  hSelectedNonempty : ∀ m, ∀ j ∈ B m, ∀ i ∈ S m j,
    ((((tubes j ∩ gain m j) ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
      Metric.ball (centers m j i) (radius m))).Nonempty
  hGreedy : ∀ m,
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m * (B m).card ≤
      2 * (Fintype.card T : ℝ)
  hCapture : ∀ m,
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * (∑ k ∈ D m, pieceMass m k)
  hVolume : ∀ m, ∀ k ∈ D m,
    pieceMass m k ≤ C * deltaPow * radius m
  hNormalization : (Fintype.card T : ℝ) * deltaPow ≤ Z
  hRadiusScale : ∀ m,
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      ((1 : ℝ) / ((n : ℝ) - 1)) * radius m ≤ radiusCap

/-- Canonical `LowerIncidence` at every dyadic level, with a representative
map quantified existentially rather than fixed by an arbitrary choice of one
Vitali ball per selected tube. No surjectivity follows solely from `g.e`. -/
def LowerIncidenceAtLevels (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) : Prop :=
  ∀ m, ∃ rep : {j : T // j ∈ g.B m} → {k : K // k ∈ g.D m},
    LowerIncidence
      (reindexedSmallPiece tubes (g.gain m)
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.centers m) (g.radius m)
        (g.B m) (g.S m) (g.D m) (g.e m)) rep



/-- Range-surjectivity of `E ∘ rep` at each level, where its codomain is
restricted to `Set.range E`, not all subsets of X. -/
def ComposedRangeCoverageAtLevels (μ : Measure X) (tubes : T → Set X)
    (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) : Prop :=
  ∀ m, ∃ rep : {j : T // j ∈ g.B m} → {k : K // k ∈ g.D m},
    Function.Surjective
      (composedIntoRange
        (reindexedSmallPiece tubes (g.gain m)
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (g.centers m) (g.radius m)
          (g.B m) (g.S m) (g.D m) (g.e m)) rep)

/-- At every dyadic level the bijection k = (g.e m).symm provides
range coverage of E ∘ k. This is proved from the equivalence itself. -/
theorem pair_map_composed_range_coverage_at_levels
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) :
    ∀ m, Function.Surjective
      (composedIntoRange
        (reindexedSmallPiece tubes (g.gain m)
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (g.centers m) (g.radius m)
          (g.B m) (g.S m) (g.D m) (g.e m))
        (g.e m).symm) := by
  intro m
  exact composedIntoRange_surjective_of_pair_equiv
    (g.B m) (g.S m) (g.D m) (g.e m)
    (reindexedSmallPiece tubes (g.gain m)
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (g.centers m) (g.radius m)
      (g.B m) (g.S m) (g.D m) (g.e m))

/-- LowerIncidence for k = e.symm at every level, following E-injectivity
and composed-range surjectivity. Its representative domain is the full
`TubeWiseVitaliLabel`, not the selected-tube subtype. -/
theorem pair_map_lower_incidence_at_levels
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) :
    ∀ m, LowerIncidence
      (reindexedSmallPiece tubes (g.gain m)
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.centers m) (g.radius m)
        (g.B m) (g.S m) (g.D m) (g.e m))
      (g.e m).symm := by
  intro m
  exact reindexed_lower_incidence_of_pair_equiv_injective
    tubes (g.gain m)
    (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m)
    (g.B m) (g.S m) (g.D m) (g.e m)
    (g.hGain m) (g.hBalls m) (g.hSelectedNonempty m)

/-- Prove E injective from disjoint/nonempty pieces; then use surjectivity
of E ∘ rep onto `Set.range E` to deduce surjectivity of rep and finally
`LowerIncidence E rep`. No selected-tube bijection is assumed. -/
theorem lowerIncidenceAtLevels_of_composed_range
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hRange : ComposedRangeCoverageAtLevels μ tubes n g) :
    LowerIncidenceAtLevels μ tubes n g := by
  intro m
  obtain ⟨rep, hRepRange⟩ := hRange m
  refine ⟨rep, ?_⟩
  exact reindexed_lower_incidence_of_composed_range
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m) (g.B m) (g.S m) (g.D m)
    (g.e m) rep (g.hGain m) (g.hBalls m)
    (g.hSelectedNonempty m) hRepRange

/-- The cardinality equality from lower incidence, separately at every dyadic
level. It is a consequence, not an independent selection hypothesis. -/
theorem exact_reindexed_cardinality_at_every_level
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hLower : LowerIncidenceAtLevels μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (g.D m).card = (g.B m).card := by
  exact reindexed_card_eq_of_lower_incidence
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m) (g.B m) (g.S m) (g.D m) (g.e m)
    (g.hNonemptyFiber m) (g.hGain m) (g.hBalls m)
    (g.hSelectedNonempty m) (hLower m)

/-- The real dyadic mass bound, no longer postulated as `hLevel`. -/
theorem dyadic_level_budget_of_lower_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hLower : LowerIncidenceAtLevels μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radius m := by
  exact reindexed_level_of_lower_incidence
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m) (g.B m) (g.S m) (g.D m) (g.e m)
    (g.hGain m) (g.hBalls m)
    (g.hSelectedNonempty m) (hLower m)
    (g.pieceMass m)
    (Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m))
    g.H g.C g.deltaPow (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Fintype.card T : ℝ) g.Z
    g.hH g.hC (g.hRadiusNonneg m) g.hDeltaPow
    (Kakeya.Eighty4.dyadicScale_pos (Fintype.card T) m).le
    (g.hGreedy m) (g.hCapture m) (g.hVolume m) g.hNormalization

/-- Combine the radius scale with the preceding q-times-level bound.
The dyadic-level constant is uniform in m. -/
theorem uniform_level_budget_of_lower_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hLower : LowerIncidenceAtLevels μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radiusCap := by
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let a : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ a := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + a) = q * q ^ a := by
    rw [Real.rpow_add hq 1 a, Real.rpow_one]
  have hBudget : q *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radius m :=
    dyadic_level_budget_of_lower_incidence μ tubes n g hLower m
  have hScaled := mul_le_mul_of_nonneg_left hBudget hqa
  have hCoef : 0 ≤ 2 * g.H * g.C * g.Z := by
    have hZ : 0 ≤ g.Z :=
      (mul_nonneg (Nat.cast_nonneg _) g.hDeltaPow).trans g.hNormalization
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) g.hH) g.hC) hZ
  have hCap := mul_le_mul_of_nonneg_left (g.hRadiusScale m) hCoef
  change q ^ (1 + a) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radiusCap
  calc
    q ^ (1 + a) *
        Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) =
        (q ^ a) * (q *
          Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
      rw [hpow]
      ring
    _ ≤ (q ^ a) * (2 * g.H * g.C * g.Z * g.radius m) := hScaled
    _ = (2 * g.H * g.C * g.Z) * (q ^ a * g.radius m) := by ring
    _ ≤ (2 * g.H * g.C * g.Z) * g.radiusCap := hCap
    _ = 2 * g.H * g.C * g.Z * g.radiusCap := by ring

/-- Main conditional Kakeya maximal-tube-sum endpoint: the level estimates
are *proved* from the single per-level lower-incidence hypothesis and the
explicit geometric inputs, rather than separately assumed. -/
theorem full_conditional_kakeya_of_lower_incidence
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hLower : LowerIncidenceAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
          ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^
          (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
          (2 * g.H * g.C * g.Z * g.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  apply logarithmic_norm_from_level_budgets μ tubes n hn
    (2 * g.H * g.C * g.Z * g.radiusCap) hT
  intro m
  exact uniform_level_budget_of_lower_incidence μ tubes n g hLower m

/-- Companion integral-moment statement (same lower-incidence hypothesis). -/
theorem full_conditional_kakeya_moment_of_lower_incidence
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hLower : LowerIncidenceAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (2 * g.H * g.C * g.Z * g.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg
    · norm_num
    · linarith
  have hMoment := logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1))
    (2 * g.H * g.C * g.Z * g.radiusCap) ha hT
    (uniform_level_budget_of_lower_incidence μ tubes n g hLower)
  obtain ⟨he, _⟩ := Kakeya.Conditional.dimension_exponents n hn
  simpa only [he] using hMoment

/-- The endpoint also follows from the user's range-composition condition. -/
theorem full_conditional_kakeya_of_composed_range
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hRange : ComposedRangeCoverageAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
          ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^
          (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
          (2 * g.H * g.C * g.Z * g.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  exact full_conditional_kakeya_of_lower_incidence μ tubes n hn g hT
    (lowerIncidenceAtLevels_of_composed_range μ tubes n g hRange)

/-- Companion moment estimate from range-surjective compositions. -/
theorem full_conditional_kakeya_moment_of_composed_range
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hRange : ComposedRangeCoverageAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (2 * g.H * g.C * g.Z * g.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  exact full_conditional_kakeya_moment_of_lower_incidence μ tubes n hn g hT
    (lowerIncidenceAtLevels_of_composed_range μ tubes n g hRange)


/-! ## Row bound: helper lemmas -/

/-- A row of a relation whose only possible column is `k₀` has weight at most 1. -/
theorem weight_le_one_of_unique {U Q : Type*} [Fintype U] [Fintype Q]
    (R : U → Q → Prop) (r : U) (k₀ : Q)
    (hUnique : ∀ k, R r k → k = k₀) :
    Kakeya.Seventy7.weight R (fun _ => (1 : ℝ)) r ≤ 1 := by
  classical
  have hBound : Kakeya.Seventy7.weight R (fun _ => (1 : ℝ)) r ≤
      Kakeya.Seventy7.weight (fun (_ : U) (k : Q) => k = k₀)
        (fun _ => (1 : ℝ)) r := by
    unfold Kakeya.Seventy7.weight
    apply Finset.sum_le_sum
    intro k _
    by_cases hR : R r k
    · have heq : k = k₀ := hUnique k hR
      subst k
      simp [hR]
    · simp [hR]
      split_ifs <;> norm_num
  have hSingleton : Kakeya.Seventy7.weight (fun (_ : U) (k : Q) => k = k₀)
      (fun _ => (1 : ℝ)) r = 1 := by
    simp [Kakeya.Seventy7.weight]
  exact hBound.trans hSingleton.le

/-- Row bound from `onePieceIncidence_iff_eq`: against a FIXED representative piece
`E (rep j)`, the row has weight at most 1. -/
theorem row_le_one_of_representative {J P : Type*} [Fintype J] [Fintype P]
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (R : J → P → Prop)
    (hR : ∀ j p, R j p ↔ (E p ∩ E (rep j)).Nonempty)
    (j : J) :
    Kakeya.Seventy7.weight R (fun _ => (1 : ℝ)) j ≤ 1 := by
  apply weight_le_one_of_unique R j (rep j)
  intro p hp
  have hInc : representativeIncidence E rep j p := (hR j p).mp hp
  exact (onePieceIncidence_iff_eq E rep hDisjoint hNonempty j p).mp hInc


/-! ## Endpoint via the manuscript's same-ball selected incidence

The lower (column) incidence is obtained from the bijective pair indexing
at every level.  The remaining row upper bound is for exactly that same
incidence relation, not for an arbitrarily selected representative piece.
-/

/-- The reindexed small pieces `E k` at level `m`, indexed by `D m`. -/
abbrev levelPiece (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    {k : K // k ∈ g.D m} → Set X :=
  reindexedSmallPiece tubes (g.gain m)
    (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m)
    (g.B m) (g.S m) (g.D m) (g.e m)

/-- Pairwise disjointness of the level pieces, from `g.hGain` and `g.hBalls`. -/
theorem levelPiece_pairwise_disjoint
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    ∀ k k' : {k : K // k ∈ g.D m}, k ≠ k' →
      Disjoint (levelPiece μ tubes n g m k) (levelPiece μ tubes n g m k') :=
  reindexedSmallPiece_pairwise_disjoint
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m) (g.B m) (g.S m) (g.D m) (g.e m)
    (g.hGain m) (g.hBalls m)

/-- The manuscript's same-ball selected incidence at level `m`. -/
abbrev sameBallAt (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    T → {k : K // k ∈ g.D m} → Prop :=
  sameBallTubeIncidence tubes (g.gain m)
    (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m)
    (g.B m) (g.S m) (g.D m) (g.e m)

/-- Row-at-most-one for the manuscript's actual incidence. This is a
separate property: pairwise-disjoint balls alone need not give it, since
a fixed selected tube can have several chosen balls. -/
def SameBallRowBoundAtLevels (μ : Measure X) (tubes : T → Set X)
    (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) : Prop :=
  ∀ m, ∀ r ∈ g.B m,
    Kakeya.Seventy7.weight (sameBallAt μ tubes n g m)
      (fun _ => (1 : ℝ)) r ≤ 1



theorem sameBallRepresentative_iff_lowerIncidence_of_parent
    {J P X : Type*} [Finite J]
    (E : P → Set X)
    (parent : P → J)
    (sameBall : J → P → Prop)
    (hDisjoint : ∀ p p' : P, p ≠ p' →
      Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hParentSurj : Function.Surjective parent)
    (hSameBall : ∀ j p,
      sameBall j p ↔ parent p = j) :
    (∃ rep : J → P,
      ∀ j p, sameBall j p ↔
        (E p ∩ E (rep j)).Nonempty) ↔
    (∃ rep : J → P, LowerIncidence E rep) := by
  classical
  constructor
  · rintro ⟨rep, hRep⟩
    refine ⟨rep, ?_⟩
    intro p
    refine ⟨parent p, ?_⟩
    exact (hRep (parent p) p).mp
      ((hSameBall (parent p) p).mpr rfl)

  · rintro ⟨rep, hLow⟩

    have hRepSurj : Function.Surjective rep := by
      intro p
      obtain ⟨j, h⟩ := hLow p
      exact ⟨j,
        ((onePieceIncidence_iff_eq
          E rep hDisjoint hNonempty j p).mp h).symm⟩

    have hCompSurj :
        Function.Surjective
          (fun j : J => parent (rep j)) := by
      intro j
      obtain ⟨p, hp⟩ := hParentSurj j
      obtain ⟨i, hi⟩ := hRepSurj p
      refine ⟨i, ?_⟩
      change parent (rep i) = j
      rw [hi]
      exact hp

    have hCompInj :
        Function.Injective
          (fun j : J => parent (rep j)) :=
      (Finite.injective_iff_surjective).2 hCompSurj

    have hParentInj : Function.Injective parent := by
      intro p p' hEq
      obtain ⟨i, hi⟩ := hRepSurj p
      obtain ⟨i', hi'⟩ := hRepSurj p'
      have hIndex : i = i' := hCompInj (by
        change parent (rep i) = parent (rep i')
        rw [hi, hi']
        exact hEq)
      calc
        p = rep i := hi.symm
        _ = rep i' := congrArg rep hIndex
        _ = p' := hi'

    let equiv : P ≃ J :=
      Equiv.ofBijective parent
        ⟨hParentInj, hParentSurj⟩

    refine ⟨equiv.symm, ?_⟩
    intro j p

    rw [hSameBall j p]
    change parent p = j ↔
      (E p ∩ E (equiv.symm j)).Nonempty
    constructor
    · intro hp
      have hp' : p = equiv.symm j := by
          apply equiv.injective
          change parent p = parent (equiv.symm j)
          calc
            parent p = j := hp
            _ = parent (equiv.symm j) := by
              change j = equiv (equiv.symm j)
              exact (equiv.apply_symm_apply j).symm
      exact (onePieceIncidence_iff_eq
        E equiv.symm hDisjoint hNonempty j p).mpr hp'
    · intro hInc
      have hp : p = equiv.symm j :=
        (onePieceIncidence_iff_eq
          E equiv.symm hDisjoint hNonempty j p).mp hInc
      rw [hp]
      change equiv (equiv.symm j) = j
      exact equiv.apply_symm_apply j

/-- THE ASSUMPTION, made visible.  At every level the same-ball test piece of a
selected tube `r` is the level piece of ONE chosen label `rep r` (one fixed
Vitali ball per selected tube).  It is not implied by `g.e`; for it to hold every
selected tube must keep exactly the balls the representative singles out. -/
def SameBallIsRepresentativeAtLevels (μ : Measure X) (tubes : T → Set X)
    (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) :
    Prop :=
  ∀ m, ∃ rep : {j : T // j ∈ g.B m} → {k : K // k ∈ g.D m},
    ∀ (r : T) (hr : r ∈ g.B m) (k : {k : K // k ∈ g.D m}),
      sameBallAt μ tubes n g m r k ↔
        (levelPiece μ tubes n g m k ∩
          levelPiece μ tubes n g m (rep ⟨r, hr⟩)).Nonempty


/-- The row bound from the visible assumption, by disjointness alone (the `→`
direction of `onePieceIncidence_iff_eq`: meeting `E (rep r)` forces `k = rep r`). -/
theorem sameBallRowBoundAtLevels_of_representative
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hRep : SameBallIsRepresentativeAtLevels μ tubes n g) :
    SameBallRowBoundAtLevels μ tubes n g := by
  classical
  intro m r hr
  obtain ⟨rep, hR⟩ := hRep m
  have hDisj := levelPiece_pairwise_disjoint μ tubes n g m
  apply weight_le_one_of_unique _ r (rep ⟨r, hr⟩)
  intro k hk
  by_contra hne
  obtain ⟨x, hx, hy⟩ := (hR r hr k).mp hk
  exact (Set.disjoint_left.mp (hDisj k (rep ⟨r, hr⟩) hne)) hx hy

/-- Column coverage (the user's count >= 1) at every dyadic level, proved
with the tube label selected by the bijection. -/
theorem same_ball_column_coverage_at_levels
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n) :
    ∀ m, ∀ k : {k : K // k ∈ g.D m},
      ∃ r ∈ g.B m,
        sameBallTubeIncidence tubes (g.gain m)
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (g.centers m) (g.radius m)
          (g.B m) (g.S m) (g.D m) (g.e m) r k := by
  intro m
  exact sameBallTubeIncidence_column_covered
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m)
    (g.B m) (g.S m) (g.D m) (g.e m) (g.hSelectedNonempty m)

/-- Real dyadic q-times-mass estimate with actual same-ball incidence. -/
theorem dyadic_level_budget_of_same_ball_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hRow : SameBallRowBoundAtLevels μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radius m := by
  exact reindexed_level_of_same_ball_incidence
    tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (g.centers m) (g.radius m) (g.B m) (g.S m) (g.D m) (g.e m)
    (g.hSelectedNonempty m) (hRow m)
    (g.pieceMass m)
    (Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m))
    g.H g.C g.deltaPow (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Fintype.card T : ℝ) g.Z
    g.hH g.hC (g.hRadiusNonneg m) g.hDeltaPow
    (Kakeya.Eighty4.dyadicScale_pos (Fintype.card T) m).le
    (g.hGreedy m) (g.hCapture m) (g.hVolume m) g.hNormalization

/-- Uniform dyadic mass estimate using same-ball lower coverage and the
row upper bound for the same incidence. -/
theorem uniform_level_budget_of_same_ball_incidence
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hRow : SameBallRowBoundAtLevels μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radiusCap := by
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let a : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ a := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + a) = q * q ^ a := by
    rw [Real.rpow_add hq 1 a, Real.rpow_one]
  have hBudget : q *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radius m :=
    dyadic_level_budget_of_same_ball_incidence μ tubes n g hRow m
  have hScaled := mul_le_mul_of_nonneg_left hBudget hqa
  have hCoef : 0 ≤ 2 * g.H * g.C * g.Z := by
    have hZ : 0 ≤ g.Z :=
      (mul_nonneg (Nat.cast_nonneg _) g.hDeltaPow).trans g.hNormalization
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) g.hH) g.hC) hZ
  have hCap := mul_le_mul_of_nonneg_left (g.hRadiusScale m) hCoef
  change q ^ (1 + a) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      2 * g.H * g.C * g.Z * g.radiusCap
  calc
    q ^ (1 + a) *
        Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) =
        (q ^ a) * (q *
          Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
      rw [hpow]
      ring
    _ ≤ (q ^ a) * (2 * g.H * g.C * g.Z * g.radius m) := hScaled
    _ = (2 * g.H * g.C * g.Z) * (q ^ a * g.radius m) := by ring
    _ ≤ (2 * g.H * g.C * g.Z) * g.radiusCap := hCap
    _ = 2 * g.H * g.C * g.Z * g.radiusCap := by ring

/-- The endpoint conditional Kakeya norm estimate using the actual
same-ball selected-incidence formula. The column lower bound is a theorem;
only the corresponding row upper bound is supplied as an incidence input. -/
theorem full_conditional_kakeya_of_same_ball_incidence
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hRow : SameBallRowBoundAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
          ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^
          (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
          (2 * g.H * g.C * g.Z * g.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  apply logarithmic_norm_from_level_budgets μ tubes n hn
    (2 * g.H * g.C * g.Z * g.radiusCap) hT
  intro m
  exact uniform_level_budget_of_same_ball_incidence μ tubes n g hRow m

/-- Companion endpoint moment bound with the same incidence. -/
theorem full_conditional_kakeya_moment_of_same_ball_incidence
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hRow : SameBallRowBoundAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (2 * g.H * g.C * g.Z * g.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg
    · norm_num
    · linarith
  have hMoment := logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1))
    (2 * g.H * g.C * g.Z * g.radiusCap) ha hT
    (uniform_level_budget_of_same_ball_incidence μ tubes n g hRow)
  obtain ⟨he, _⟩ := Kakeya.Conditional.dimension_exponents n hn
  simpa only [he] using hMoment

/-- The same-ball endpoint from the visible representative assumption: row bound by
disjointness, column coverage by the bijective pair indexing. -/
theorem full_conditional_kakeya_of_same_ball_representative
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (g : LocalizedDyadicInputs (X := X) (T := T) (I := I) (K := K) μ tubes n)
    (hT : ∀ i, MeasurableSet (tubes i))
    (hRep : SameBallIsRepresentativeAtLevels μ tubes n g) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
          ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^
          (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
          (2 * g.H * g.C * g.Z * g.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) :=
  full_conditional_kakeya_of_same_ball_incidence μ tubes n hn g hT
    (sameBallRowBoundAtLevels_of_representative μ tubes n g hRep)

end Kakeya.Eighty9
