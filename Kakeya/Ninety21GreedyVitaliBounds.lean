module

public import Kakeya.Ninety21GreedyVitaliIntegration

/-!
# Bounds for the greedy–Vitali retained geometry

The analytic volume and dyadic-cardinality fields of `ConcreteTubeBallBounds`
follow from the constructed retained pieces. Occupancy is established from
centers belonging to the dyadic band. The original-tube incidence estimate
remains a separate geometric input.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- The dyadic radius used for finite-net localization. -/
noncomputable def canonicalGreedyVitaliRadius
    {T : Type*} [Fintype T] (n : ℕ) (A : ℝ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : ℝ :=
  A * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
    (-((1 : ℝ) / ((n : ℝ) - 1)))

/-- A positive radius parameter gives positive localization radii. -/
theorem canonicalGreedyVitaliRadius_pos
    {T : Type*} [Fintype T] (n : ℕ) (A : ℝ) (hA : 0 < A)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    0 < canonicalGreedyVitaliRadius (T := T) n A m := by
  unfold canonicalGreedyVitaliRadius
  exact mul_pos hA
    (Real.rpow_pos_of_pos (Kakeya.Eighty4.dyadicScale_pos _ m) _)

/-- The canonical localization radius has exact dyadic scaling. -/
theorem canonicalGreedyVitaliRadius_scale
    {T : Type*} [Fintype T] (n : ℕ) (A : ℝ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
      ((1 : ℝ) / ((n : ℝ) - 1)) *
      canonicalGreedyVitaliRadius (T := T) n A m = A := by
  exact canonical_retained_radius_scale n (Fintype.card T) A m

/-- A radius-R ball centered on the dyadic level is occupied by that level. -/
theorem ConcreteGreedyVitaliCandidates.retained_ball_occupied_of_centers
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hCenters : ∀ m i,
      d.centers m i ∈ Kakeya.Eighty4.concreteDyadicBand tubes m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin (d.retained.ballCount m)) :
    (d.retained.ball m i ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty := by
  refine ⟨d.centers m i, ?_, hCenters m i⟩
  rw [d.retained_ball_eq m i, d.hBall m i]
  exact Metric.mem_ball_self (d.hRadius m)

/-- The radius-R localization ball of every retained label meets its dyadic level. -/
theorem ConcreteGreedyVitaliCandidates.retained_label_ball_occupied
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ d.retained.B m} ⊕
      {p : T × ℕ // p ∈ d.retained.P m}) :
    (d.retained.ball m (d.retained.ballOf m s) ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty := by
  obtain ⟨x, hx⟩ := d.retained_piece_nonempty m s
  exact ⟨x, d.retained.piece_subset_ball m s hx,
    d.retained.piece_subset_level m s hx⟩

/-- Restricting to tubes with occupied selected balls preserves the
original selected-tube cardinality bound. -/
theorem ConcreteGreedyVitaliCandidates.retained_selected_card_le
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (d.retained.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
  exact (g.activeVitaliTubes_card_le d.selected m).trans (hSelected m)

/-- The original maximizing greedy selection supplies the selected-cardinality
bound for the occupied retained subfamily. -/
theorem ConcreteGreedyVitaliCandidates.retained_selected_card_maximal_unused
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hB : ∀ m, g.B m = maximalUnusedDyadicSelected μ tubes m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (d.retained.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
  apply d.retained_selected_card_le
    (fun m' => by rw [hB m', maximalUnusedDyadicSelected_card])

/-- Genuine finite-net centers lie on the dyadic level of their parent gain. -/
theorem ofGreedyNetFamily_center_on_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (C : ∀ m, T → Finset X)
    (hCenters : ∀ m j, j ∈ B m → ∀ c ∈ C m j,
      c ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin (Fintype.card (VitaliFiniteCenterPair (B m) (C m)))) :
    vitaliFiniteCenter (B m) (C m) i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := by
  let p : VitaliFiniteCenterPair (B m) (C m) :=
    vitaliFiniteCenterEquiv (B m) (C m) i
  have hx := hCenters m p.1.1 p.1.2 p.2.1 p.2.2
  have hLevel := Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (chosen m) (stage m p.1.1) hx
  exact hLevel

/-- The unpadded finite-net geometry has only centers belonging to
actual greedy gains, hence to the dyadic level. -/
theorem ofGreedyNetFamilyAllowEmpty_center_on_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (hCenters : ∀ m j, j ∈ B m → ∀ c ∈ C m j,
      c ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin ((ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty
      tubes B chosen stage hChosen C radius).ballCount m)) :
    vitaliFiniteCenter (activeGainNetTubes B C m) (C m) i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := by
  exact ofGreedyNetFamily_center_on_level tubes
    (activeGainNetTubes B C) chosen stage C
    (fun m j hj c hc => hCenters m j (Finset.mem_filter.mp hj).1 c hc)
    m i

/-- The compact greedy-gain construction satisfies the center-occupancy
condition without auxiliary ball indices. -/
theorem compactGreedyGain_centers_on_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [ProperSpace X] [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin ((ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty
      tubes B chosen stage hChosen
      (greedyFiniteNet tubes chosen stage radius hRadius hBound)
      radius).ballCount m)) :
    vitaliFiniteCenter
        (activeGainNetTubes B
          (greedyFiniteNet tubes chosen stage radius hRadius hBound) m)
        (greedyFiniteNet tubes chosen stage radius hRadius hBound m) i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := by
  exact ofGreedyNetFamilyAllowEmpty_center_on_level tubes B chosen stage
    hChosen (greedyFiniteNet tubes chosen stage radius hRadius hBound)
    (fun m j _ c hc => greedyFiniteNet_mem tubes chosen stage radius
      hRadius hBound m j c hc) radius m i

/-- The compact-gain candidate data inherits occupied centers directly
from the finite-net construction. -/
theorem ConcreteGreedyVitaliCandidates.ofCompactGreedyGains_centers_on_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [ProperSpace X] [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (hStages : ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      chosen m k ∈ B m ∧ stage m (chosen m k) = k) :
    let d := ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
      tubes B chosen stage hChosen radius hRadius hBound hStages
    ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m := by
  dsimp only
  intro m i
  exact compactGreedyGain_centers_on_level
    tubes B chosen stage hChosen radius hRadius hBound m i

/-- Every ball of the compact-gain retained geometry is occupied.
Empty gain levels have no ball indices. -/
theorem ConcreteGreedyVitaliCandidates.ofCompactGreedyGains_retained_ball_occupied
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [ProperSpace X] [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (hStages : ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      chosen m k ∈ B m ∧ stage m (chosen m k) = k) :
    let d := ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
      tubes B chosen stage hChosen radius hRadius hBound hStages
    ∀ m i, (d.retained.ball m i ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty := by
  dsimp only
  intro m i
  let d := ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
    tubes B chosen stage hChosen radius hRadius hBound hStages
  exact d.retained_ball_occupied_of_centers
    (ConcreteGreedyVitaliCandidates.ofCompactGreedyGains_centers_on_level
      tubes B chosen stage hChosen radius hRadius hBound hStages)
    m i

/-- The retained small piece is bounded by the ordinary radius-R
Euclidean tube–ball volume estimate. -/
theorem ConcreteGreedyVitaliCandidates.retained_piece_euclidean_cost
    {k : ℕ} {T : Type*} [Fintype T]
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
    (C : ℝ) (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ d.retained.B m} ⊕
      {p : T × ℕ // p ∈ d.retained.P m}) :
    Kakeya.Conditional.mass μ (d.retained.piece m s) ≤
      C * δ ^ (k + 1) * d.radius m := by
  let E := d.retained.piece m s
  let R := d.radius m
  let j := d.retained.tubeOf m s
  let i := d.retained.ballOf m s
  let ω := tripleRadiusTransverseCoefficient k
  have hR : 0 ≤ R := (d.hRadius m).le
  have hBall : d.retained.ball m i ⊆ Metric.closedBall (d.centers m i) R := by
    intro x hx
    have hb : x ∈ Metric.ball (d.centers m i) R := by
      rw [← d.hBall m i, ← d.retained_ball_eq m i]
      exact hx
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hb))
  have hVolume :
      (volume : Measure (Kakeya.Space (k + 2))) E ≤
        ENNReal.ofReal (2 * R) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
    exact d.retained.piece_volume_le_explicit center direction δ m s
      (d.centers m i) R hR (hv j) hBall
  have hBallMeasurable : ∀ m i, MeasurableSet (d.retained.ball m i) := by
    intro m i
    rw [d.retained_ball_eq m i, d.hBall m i]
    exact Metric.isOpen_ball.measurableSet
  have hTrimMeasurable : ∀ m j i,
      MeasurableSet (d.retained.trim m j i) := by
    intro m j i
    change MeasurableSet (Set.univ : Set (Kakeya.Space (k + 2)))
    exact MeasurableSet.univ
  have hE : MeasurableSet E :=
    d.retained.piece_measurable hT hBallMeasurable hTrimMeasurable m s
  have hMeasured : Kakeya.Conditional.mass μ E = (μ E).toReal :=
    conditional_mass_eq_measure_toReal μ E hE
  have hReal : (μ E).toReal ≤
      (ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))).toReal := by
    have hFinite :
        ENNReal.ofReal (2 * R) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      apply ENNReal.mul_ne_top
      · intro ht
        exact ENNReal.ofReal_ne_top (ENNReal.pow_eq_top_iff.mp ht).1
      · exact ENNReal.ofReal_ne_top
    exact ENNReal.toReal_mono hFinite ((hDom E).trans hVolume)
  have hRealBound : (μ E).toReal ≤ 2 * R * (δ ^ (k + 1) * ω) := by
    have h2R : 0 ≤ 2 * R := by positivity
    simpa only [ω, tripleRadiusTransverseCoefficient,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal h2R, ENNReal.toReal_ofReal hδ] using hReal
  have hNonneg : 0 ≤ R * δ ^ (k + 1) :=
    mul_nonneg hR (pow_nonneg hδ _)
  have hConst : (2 * ω) * (R * δ ^ (k + 1)) ≤
      C * (R * δ ^ (k + 1)) :=
    mul_le_mul_of_nonneg_right hCgeom hNonneg
  calc
    Kakeya.Conditional.mass μ E = (μ E).toReal := hMeasured
    _ ≤ 2 * R * (δ ^ (k + 1) * ω) := hRealBound
    _ = (2 * ω) * (R * δ ^ (k + 1)) := by ring
    _ ≤ C * (R * δ ^ (k + 1)) := hConst
    _ = C * δ ^ (k + 1) * R := by ring

/-- Supply the concrete bounds for the same occupied retained labels.
The ball-incidence estimate and normalization remain geometric inputs. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds
    {k : ℕ} {T : Type*} [Fintype T]
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
    (hRadius : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))))
    (hCenters : ∀ m i,
      d.centers m i ∈ Kakeya.Eighty4.concreteDyadicBand
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hScale : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        (Fintype.card T : ℝ))
    (hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z)
    (hIncidence : ∀ m r,
      (∑ i : Fin (d.retained.ballCount m),
        if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
            {p : T × ℕ // p ∈ d.retained.P m}),
          d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
        then (1 : ℝ) else 0) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) :
    ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained := by
  refine {
    hNonempty := d.retained_piece_nonempty
    hBallOccupied := d.retained_ball_occupied_of_centers hCenters
    C := C
    A := A
    deltaPow := δ ^ (k + 1)
    Z := Z
    ballPackingConstant := K
    hC := hC
    hA := hA
    hDeltaPow := pow_nonneg hδ _
    hScaleLe := hScale
    hSelectedCard := d.retained_selected_card_le hSelected
    hVolume := ?_
    hNormalization := hNorm
    hBallPackingConstant := hK
    hHallRight := ?_
  }
  · intro m s
    have hVolume := d.retained_piece_euclidean_cost μ center direction δ hδ g
      hT hv hDom C hCgeom m s
    calc
      Kakeya.Conditional.mass μ (d.retained.piece m s) ≤
          C * δ ^ (k + 1) * d.radius m := hVolume
      _ = C * δ ^ (k + 1) *
            (A * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
              (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)))) := by rw [hRadius m]
  · intro m r
    exact hIncidence m r

/-- The radius in the derived concrete bounds is the radius of the
original finite gain nets. -/
theorem ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds_radius
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (A : ℝ) (hA : b.A = A)
    (hRadius : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    d.radius m = twoRadiusRadius d.retained b m := by
  rw [hRadius m]
  rw [twoRadiusRadius, hA]

end Kakeya.Ninety21
