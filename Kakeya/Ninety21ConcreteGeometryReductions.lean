module

public import Kakeya.Ninety21ConcreteTubeBallBridge
public import Kakeya.Eighty9ArbitraryOrientationTubeBall

/-!
# Geometric estimates for indexed retained pieces

The volume estimate uses the actual Euclidean unit tube. Finite Vitali selection
transfers an original localization cover to enlarged selected balls.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- The cardinality bound for the selected original tubes follows from the
ceiling count in the greedy construction. -/
theorem ConcreteTubeBallGeometry.greedy_card_budget
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hqN : Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
      (Fintype.card T : ℝ))
    (hSelected : (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m * (g.B m).card ≤
      2 * (Fintype.card T : ℝ) := by
  exact Kakeya.Eighty9.greedy_selected_card_budget (g.B m)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) hqN hSelected

/-- The usual dyadic radius has exactly the prescribed scaling. -/
theorem canonical_retained_radius_scale
    (n N : ℕ) (C : ℝ)
    (m : Kakeya.Eighty4.DyadicIndex N) :
    Kakeya.Eighty4.dyadicScale N m ^ ((1 : ℝ) / ((n : ℝ) - 1)) *
      (C * Kakeya.Eighty4.dyadicScale N m ^
        (-((1 : ℝ) / ((n : ℝ) - 1)))) = C := by
  exact Kakeya.Eighty9.canonical_dyadic_radius_scale n N C m

/-- The localized retained piece obeys the orientation-independent tube–ball
measure bound whenever its localization ball has the stated Euclidean center
and radius. -/
theorem ConcreteTubeBallGeometry.piece_volume_le_orthogonal_product
    {n : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space n) (δ : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})
    (b : Kakeya.Space n) (R : ℝ)
    (hBall : g.ball m (g.ballOf m s) ⊆ Metric.closedBall b R) :
    (volume : Measure (Kakeya.Space n)) (g.piece m s) ≤
      (volume : Measure ↥(Kakeya.TubeBall.directionLine
        (direction (g.tubeOf m s))))
        (Metric.closedBall
          (Kakeya.TubeBall.directionCoordinates
            (center (g.tubeOf m s)) (direction (g.tubeOf m s)) b).1 R) *
      (volume : Measure ↥((Kakeya.TubeBall.directionLine
        (direction (g.tubeOf m s)))ᗮ))
        (Metric.closedBall 0 δ) := by
  have hsub : g.piece m s ⊆
      Kakeya.unitTube (center (g.tubeOf m s))
        (direction (g.tubeOf m s)) δ ∩ Metric.closedBall b R := by
    intro x hx
    exact ⟨g.piece_subset_tube m s hx,
      hBall (g.piece_subset_ball m s hx)⟩
  exact (measure_mono hsub).trans
    (Kakeya.TubeBall.unitTube_ball_volume_le_orthogonal_product
      (center (g.tubeOf m s)) (direction (g.tubeOf m s)) b δ R)

/-- Explicit transverse-dimensional form of the retained-piece volume bound. -/
theorem ConcreteTubeBallGeometry.piece_volume_le_explicit
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2)) (δ : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})
    (b : Kakeya.Space (k + 2)) (R : ℝ)
    (hR : 0 ≤ R)
    (hv : direction (g.tubeOf m s) ≠ 0)
    (hBall : g.ball m (g.ballOf m s) ⊆ Metric.closedBall b R) :
    (volume : Measure (Kakeya.Space (k + 2))) (g.piece m s) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
  let j := g.tubeOf m s
  calc
    (volume : Measure (Kakeya.Space (k + 2))) (g.piece m s) ≤
        (volume : Measure ↥(Kakeya.TubeBall.directionLine (direction j)))
          (Metric.closedBall
            (Kakeya.TubeBall.directionCoordinates (center j) (direction j) b).1 R) *
        (volume : Measure ↥((Kakeya.TubeBall.directionLine (direction j))ᗮ))
          (Metric.closedBall 0 δ) := by
            exact g.piece_volume_le_orthogonal_product center direction δ m s b R hBall
    _ = ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
          rw [Kakeya.TubeBall.directionLine_closedBall_volume
                (center j) (direction j) b R hv hR,
              Kakeya.TubeBall.transverse_closedBall_volume
                (direction j) δ hv]

/-- A finite original localization cover yields a cover by selected Vitali
balls of triple radius. The selected undilated balls are disjoint within each
tube fiber. -/
theorem exists_concrete_vitali_localized_cover
    {X T I : Type*} [MetricSpace X]
    (B : Finset T) (L : T → Finset I)
    (centers : T → I → X) (R : ℝ) (hR : 0 < R)
    (tube gain : T → Set X) (F U : Set X)
    (hOriginal : U ⊆ ⋃ j ∈ B, ⋃ i ∈ L j,
      (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (centers j i) R)) :
    ∃ S : T → Finset I,
      (∀ j ∈ B, S j ⊆ L j) ∧
      (∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (Metric.ball (centers j i) R)
          (Metric.ball (centers j i') R)) ∧
      U ⊆ ⋃ j ∈ B, ⋃ d ∈ S j,
        (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (centers j d) (3 * R)) := by
  obtain ⟨S, hSub, hDisjoint, hVitali⟩ :=
    Kakeya.Eighty9.exists_tubeWise_equal_radius_vitali
      B L centers R hR
  refine ⟨S, hSub, hDisjoint, ?_⟩
  exact Kakeya.Eighty9.localized_cover_transfers_to_vitali
    B L S tube gain F U centers R hOriginal hVitali

/-- The union of the first `k + 1` greedy gains adds precisely the next gain. -/
theorem concrete_greedyUnion_succ
    {X : Type*} (Q : ℕ → Set X) (k : ℕ) :
    Kakeya.Eighty4.greedyUnion Q (k + 1) =
      Kakeya.Eighty4.greedyUnion Q k ∪ Q k := by
  ext x
  constructor
  · intro hx
    change x ∈ ⋃ i ∈ Finset.range (k + 1), Q i at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hik, hxi⟩ := Set.mem_iUnion.mp hi
    rcases (Nat.lt_succ_iff_lt_or_eq.mp (Finset.mem_range.mp hik)) with hlt | heq
    · left
      exact Set.mem_iUnion.mpr
        ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hlt, hxi⟩⟩
    · right
      simpa [heq] using hxi
  · intro hx
    rcases hx with hx | hx
    · change x ∈ ⋃ i ∈ Finset.range k, Q i at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hik, hxi⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr
        ⟨i, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hik)), hxi⟩⟩
    · exact Set.mem_iUnion.mpr
        ⟨k, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_self k), hx⟩⟩

/-- A new greedy gain lies outside all previously chosen tube gains. -/
theorem ConcreteTubeBallGeometry.greedyQ_subset_residual
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    g.greedyQ m k ⊆
      Kakeya.Eighty4.concreteDyadicBand tubes m \
        Kakeya.Eighty4.greedyUnion (g.greedyQ m) k := by
  intro x hx
  refine ⟨g.greedyQ_subset_level m k hx, ?_⟩
  intro hxU
  change x ∈ ⋃ i ∈ Finset.range k, g.greedyQ m i at hxU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
  obtain ⟨hik, hxi⟩ := Set.mem_iUnion.mp hi
  have hTube : x ∈ tubes (g.chosen m i) :=
    Kakeya.Eighty4.concreteGreedyGain_subset_tube tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.chosen m) i hxi
  change x ∈ (Kakeya.Eighty4.concreteDyadicBand tubes m ∩
      tubes (g.chosen m k)) \
    (⋃ i ∈ Finset.range k, tubes (g.chosen m i)) at hx
  exact hx.2 (Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr ⟨hik, hTube⟩⟩)

/-- Finite-measure conservation for the actual greedy gains. -/
theorem ConcreteTubeBallGeometry.greedy_residual_conservation
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (hT : ∀ j, MeasurableSet (tubes j))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.greedyQ m) (k + 1) =
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.greedyQ m) k - Kakeya.Conditional.mass μ (g.greedyQ m k) := by
  let F := Kakeya.Eighty4.concreteDyadicBand tubes m
  let Q := g.greedyQ m
  have hF : MeasurableSet F :=
    Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m
  have hQ : ∀ j, MeasurableSet (Q j) :=
    g.greedyQ_measurable hT m
  have hU : MeasurableSet (Kakeya.Eighty4.greedyUnion Q k) :=
    Kakeya.Eighty4.greedyUnion_measurable Q hQ k
  have hSub : Q k ⊆ F \
      Kakeya.Eighty4.greedyUnion Q k :=
    g.greedyQ_subset_residual m k
  have hMass := Kakeya.Eighty4.mass_eq_covered_add_residual
    μ (F \ Kakeya.Eighty4.greedyUnion Q k) (Q k)
    (hF.diff hU) (hQ k) hSub
  have hDiff : (F \ Kakeya.Eighty4.greedyUnion Q k) \ Q k =
      F \ Kakeya.Eighty4.greedyUnion Q (k + 1) := by
    rw [concrete_greedyUnion_succ]
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, not_or, and_assoc]
  calc
    Kakeya.Eighty4.greedyResidual μ F Q (k + 1) =
        Kakeya.Conditional.mass μ
          ((F \ Kakeya.Eighty4.greedyUnion Q k) \ Q k) := by
            rw [hDiff]
            rfl
    _ = Kakeya.Eighty4.greedyResidual μ F Q k -
          Kakeya.Conditional.mass μ (Q k) := by
            change Kakeya.Conditional.mass μ
              ((F \ Kakeya.Eighty4.greedyUnion Q k) \ Q k) =
              Kakeya.Conditional.mass μ (F \ Kakeya.Eighty4.greedyUnion Q k) -
                Kakeya.Conditional.mass μ (Q k)
            linarith

/-- The one-step greedy recurrence follows from the maximal-gain averaging
estimate and finite-measure conservation at the selected step. -/
theorem ConcreteTubeBallGeometry.greedy_recurrence_of_average
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hN : 0 < (Fintype.card T : ℝ))
    (hAverage : ∀ k,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
        (Fintype.card T : ℝ) *
          Kakeya.Conditional.mass μ (g.greedyQ m k))
    (hT : ∀ j, MeasurableSet (tubes j)) :
    ∀ k,
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.greedyQ m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.greedyQ m) k := by
  intro k
  exact Kakeya.Eighty4.greedy_step_of_average
    (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Kakeya.Eighty4.greedyResidual μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k)
    (Kakeya.Conditional.mass μ (g.greedyQ m k))
    (Kakeya.Eighty4.greedyResidual μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) (k + 1))
    hN (hAverage k) (g.greedy_residual_conservation μ hT m k)

/-- Transfer a Vitali cover to the retained indexed family when every
selected enlarged localization is represented by a retained label. -/
theorem ConcreteTubeBallGeometry.cover_of_vitali_labels
    {X T I : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (S : T → Finset I) (centers : T → I → X) (R : ℝ) (U : Set X)
    (hVitali : U ⊆ ⋃ j ∈ g.B m, ⋃ d ∈ S j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
        Metric.ball (centers j d) (3 * R)))
    (hLabels : ∀ j ∈ g.B m, ∀ d ∈ S j,
      ∃ s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m},
        (((tubes j ∩ g.gain m j) ∩
          Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
          Metric.ball (centers j d) (3 * R)) ⊆ g.piece m s) :
    U ⊆ ⋃ s, g.piece m s := by
  intro x hx
  have hxVitali := hVitali hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxVitali
  obtain ⟨hjB, hjx⟩ := Set.mem_iUnion.mp hj
  obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hjx
  obtain ⟨hdS, hxd⟩ := Set.mem_iUnion.mp hd
  obtain ⟨s, hs⟩ := hLabels j hjB d hdS
  exact Set.mem_iUnion.mpr ⟨s, hs hxd⟩

/-- Build the greedy endpoint data from the maximizing-gain average, using
finite-measure conservation for its recurrence. -/
theorem ConcreteTubeBallGreedy.ofAverage
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    {tubes : T → Set X} (n : ℕ) (g : ConcreteTubeBallGeometry tubes)
    (hN : 0 < (Fintype.card T : ℝ))
    (hScaleLe : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤ (Fintype.card T : ℝ))
    (hAverage : ∀ m k,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
        (Fintype.card T : ℝ) * Kakeya.Conditional.mass μ (g.greedyQ m k))
    (hCover : ∀ m, Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
        ⋃ p, g.piece m p)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hBall : ∀ m i, MeasurableSet (g.ball m i))
    (hTrim : ∀ m j i, MeasurableSet (g.trim m j i)) :
    ConcreteTubeBallGreedy μ tubes n g := by
  exact {
    hScaleLe := hScaleLe
    hStep := by
      intro m k
      exact g.greedy_recurrence_of_average μ m hN (hAverage m) hT k
    hCover := hCover
    hT := hT
    hBall := hBall
    hTrim := hTrim
  }

end Kakeya.Ninety21
