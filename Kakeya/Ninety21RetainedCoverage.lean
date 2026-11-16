module

public import Kakeya.Ninety21ConcreteGeometryReductions

/-!
# Vitali localization at two radii

The radius-`R` balls supply the disjoint selected indices and the tube–ball
incidence count. Their radius-`3R` enlargements cover the localized gains.
Finite subadditivity bounds the mass of this cover without identifying it
with the radius-`R` trimmed retained pieces.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

/-- Finite subadditivity for a doubly indexed family of measurable-space sets. -/
theorem finite_double_union_measure_le
    {X J I : Type*} [MeasurableSpace X]
    (μ : Measure X) (B : Finset J) (S : J → Finset I)
    (E : J → I → Set X) :
    μ (⋃ j ∈ B, ⋃ i ∈ S j, E j i) ≤
      ∑ j ∈ B, ∑ i ∈ S j, μ (E j i) := by
  calc
    μ (⋃ j ∈ B, ⋃ i ∈ S j, E j i) ≤
        ∑ j ∈ B, μ (⋃ i ∈ S j, E j i) :=
      measure_biUnion_finset_le B (fun j => ⋃ i ∈ S j, E j i)
    _ ≤ ∑ j ∈ B, ∑ i ∈ S j, μ (E j i) := by
      apply Finset.sum_le_sum
      intro j hj
      exact measure_biUnion_finset_le (S j) (E j)

/-- Vitali's triple-radius cover bounds mass by the selected enlarged
  tube–ball intersections. The original counting balls are unchanged. -/
theorem ConcreteTubeBallGeometry.measure_le_tripleBall_sum
    {X T I : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (S : T → Finset I) (centers : T → I → X) (R : ℝ) (U : Set X)
    (hVitali : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ S j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
        Metric.ball (centers j i) (3 * R))) :
    μ U ≤ ∑ j ∈ g.B m, ∑ i ∈ S j,
      μ (tubes j ∩ Metric.ball (centers j i) (3 * R)) := by
  let E : T → I → Set X := fun j i =>
    (((tubes j ∩ g.gain m j) ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
      Metric.ball (centers j i) (3 * R))
  calc
    μ U ≤ μ (⋃ j ∈ g.B m, ⋃ i ∈ S j, E j i) :=
      measure_mono hVitali
    _ ≤ ∑ j ∈ g.B m, ∑ i ∈ S j, μ (E j i) :=
      finite_double_union_measure_le μ (g.B m) S E
    _ ≤ ∑ j ∈ g.B m, ∑ i ∈ S j,
        μ (tubes j ∩ Metric.ball (centers j i) (3 * R)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      apply measure_mono
      intro x hx
      exact ⟨hx.1.1.1, hx.2⟩

/-- Select disjoint radius-`R` balls and transfer their cover to radius `3R`.
  The measure bound is applied only to enlarged intersections. -/
theorem ConcreteTubeBallGeometry.exists_twoRadius_vitali_mass_bound
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (centers : Fin (g.ballCount m) → X) (R : ℝ) (hR : 0 < R)
    (L : T → Finset (Fin (g.ballCount m))) (U : Set X)
    (hBall : ∀ i, g.ball m i = Metric.ball (centers i) R)
    (hOriginal : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ L j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ g.ball m i)) :
    ∃ S : T → Finset (Fin (g.ballCount m)),
      (∀ j ∈ g.B m, S j ⊆ L j) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (g.ball m i) (g.ball m i')) ∧
      (U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ S j,
        (((tubes j ∩ g.gain m j) ∩
          Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
          Metric.ball (centers i) (3 * R))) ∧
      μ U ≤ ∑ j ∈ g.B m, ∑ i ∈ S j,
        μ (tubes j ∩ Metric.ball (centers i) (3 * R)) := by
  have hOriginalMetric :
      U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ L j,
        (((tubes j ∩ g.gain m j) ∩
          Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
          Metric.ball (centers i) R) := by
    simpa only [hBall] using hOriginal
  obtain ⟨S, hSubset, hDisjoint, hVitali⟩ :=
    exists_concrete_vitali_localized_cover (g.B m) L
      (fun (_ : T) i => centers i) R hR tubes (g.gain m)
      (Kakeya.Eighty4.concreteDyadicBand tubes m) U hOriginalMetric
  refine ⟨S, hSubset, ?_, hVitali, ?_⟩
  · intro j hj i hi i' hi' hne
    simpa only [hBall] using hDisjoint j hj i hi i' hi' hne
  · exact g.measure_le_tripleBall_sum μ m S
      (fun (_ : T) i => centers i) R U hVitali

/-- Explicit cost of an enlarged localization for a Euclidean unit tube. -/
theorem unitTube_tripleBall_volume_le
    {k : ℕ} (p v b : Kakeya.Space (k + 2)) (δ R : ℝ)
    (hv : v ≠ 0) (hR : 0 ≤ R) :
    (volume : Measure (Kakeya.Space (k + 2)))
        (Kakeya.unitTube p v δ ∩ Metric.ball b (3 * R)) ≤
      ENNReal.ofReal (2 * (3 * R)) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
  have hSubset :
      Kakeya.unitTube p v δ ∩ Metric.ball b (3 * R) ⊆
        Kakeya.unitTube p v δ ∩ Metric.closedBall b (3 * R) := by
    intro x hx
    exact ⟨hx.1, Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hx.2))⟩
  exact (measure_mono hSubset).trans
    (Kakeya.TubeBall.unitTube_ball_volume_le_explicit_arbitrary_direction
      k p v b δ (3 * R) hv (mul_nonneg (by norm_num) hR))

/-- The mass of a localized greedy-gain cover is bounded by a volume cost per
  selected radius-`R` Vitali label, calculated using its triple-radius ball. -/
theorem ConcreteTubeBallGeometry.volume_le_tripleBall_cost
    {k : ℕ} {T I : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2)) (δ R : ℝ)
    (hv : ∀ j, direction j ≠ 0) (hR : 0 ≤ R)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (S : T → Finset I) (centers : T → I → Kakeya.Space (k + 2))
    (U : Set (Kakeya.Space (k + 2)))
    (hVitali : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ S j,
      (((Kakeya.unitTube (center j) (direction j) δ ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand
          (fun j => Kakeya.unitTube (center j) (direction j) δ) m) ∩
        Metric.ball (centers j i) (3 * R))) :
    (volume : Measure (Kakeya.Space (k + 2))) U ≤
      ∑ j ∈ g.B m, ∑ i ∈ S j,
        (ENNReal.ofReal (2 * (3 * R)) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))) := by
  calc
    (volume : Measure (Kakeya.Space (k + 2))) U ≤
        ∑ j ∈ g.B m, ∑ i ∈ S j,
          (volume : Measure (Kakeya.Space (k + 2)))
            (Kakeya.unitTube (center j) (direction j) δ ∩
              Metric.ball (centers j i) (3 * R)) :=
      g.measure_le_tripleBall_sum volume m S centers R U hVitali
    _ ≤ ∑ j ∈ g.B m, ∑ i ∈ S j,
        (ENNReal.ofReal (2 * (3 * R)) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact unitTube_tripleBall_volume_le (center j) (direction j)
        (centers j i) δ R (hv j) hR

/-- Vitali selection and the Euclidean volume estimate for the same selected
  indices. The packing and incidence balls retain radius `R`. -/
theorem ConcreteTubeBallGeometry.exists_twoRadius_vitali_volume_bound
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2)) (δ R : ℝ)
    (hv : ∀ j, direction j ≠ 0) (hR : 0 < R)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (centers : Fin (g.ballCount m) → Kakeya.Space (k + 2))
    (L : T → Finset (Fin (g.ballCount m)))
    (U : Set (Kakeya.Space (k + 2)))
    (hBall : ∀ i, g.ball m i = Metric.ball (centers i) R)
    (hOriginal : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ L j,
      (((Kakeya.unitTube (center j) (direction j) δ ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand
          (fun j => Kakeya.unitTube (center j) (direction j) δ) m) ∩
        g.ball m i)) :
    ∃ S : T → Finset (Fin (g.ballCount m)),
      (∀ j ∈ g.B m, S j ⊆ L j) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (g.ball m i) (g.ball m i')) ∧
      (volume : Measure (Kakeya.Space (k + 2))) U ≤
        ∑ j ∈ g.B m, ∑ i ∈ S j,
          (ENNReal.ofReal (2 * (3 * R)) *
            (ENNReal.ofReal δ ^ (k + 1) *
              ENNReal.ofReal
                (√Real.pi ^ (k + 1) /
                  Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))) := by
  obtain ⟨S, hSubset, hDisjoint, hVitali, _⟩ :=
    g.exists_twoRadius_vitali_mass_bound volume m centers R hR L U
      hBall hOriginal
  refine ⟨S, hSubset, hDisjoint, ?_⟩
  exact g.volume_le_tripleBall_cost center direction δ R hv hR.le
    m S (fun (_ : T) i => centers i) U hVitali

end Kakeya.Ninety21
