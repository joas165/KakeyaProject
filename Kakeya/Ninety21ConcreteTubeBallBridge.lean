module

public import Kakeya.Ninety21RegularBudget
public import Kakeya.Eighty9GeometryDischarges

/-!
# Concrete retained tube–ball pieces

The pieces are defined using original tubes, dyadic bands, greedy gains,
localization balls, and the trimming sets. Tube–ball pairs are the labels of
the remaining pieces. The construction retains these labels under reindexing.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T : Type*} [MeasurableSpace X] [Fintype T]

/-- Tube–ball labels, including a chosen localization ball for each selected label. -/
structure ConcreteTubeBallGeometry (tubes : T → Set X) where
  B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T
  P : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset (T × ℕ)
  ballCount : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ
  ball : ∀ m, Fin (ballCount m) → Set X
  chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T
  stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ
  hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j
  hPSelected : ∀ m (p : T × ℕ), p ∈ P m → p.1 ∈ B m
  hPBall : ∀ m (p : T × ℕ), p ∈ P m → p.2 < ballCount m
  selectedBall : ∀ m, {r : T // r ∈ B m} → Fin (ballCount m)
  trim : ∀ m, T → Fin (ballCount m) → Set X

/-- The parent tube of a selected or remaining retained label. -/
def ConcreteTubeBallGeometry.tubeOf
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) : T :=
  match s with
  | Sum.inl r => r.val
  | Sum.inr p => p.val.1

/-- The localization ball of a retained tube–ball label. -/
def ConcreteTubeBallGeometry.ballOf
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    Fin (g.ballCount m) :=
  match s with
  | Sum.inl r => g.selectedBall m r
  | Sum.inr p => ⟨p.val.2, g.hPBall m p.val p.property⟩

/-- The gain at a greedy step of the original tube selection. -/
def ConcreteTubeBallGeometry.greedyQ
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) : Set X :=
  Kakeya.Eighty4.concreteGreedyGain tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.chosen m) k

/-- A greedy gain at a selected tube, extended by the empty set elsewhere. -/
def ConcreteTubeBallGeometry.gain
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) : Set X :=
  if j ∈ g.B m then
    Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.chosen m) (g.stage m j)
  else ∅

/-- The trimmed, localized tube–ball intersection indexed by a retained label. -/
def ConcreteTubeBallGeometry.piece
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) : Set X :=
  (((tubes (g.tubeOf m s) ∩ g.gain m (g.tubeOf m s)) ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ g.ball m (g.ballOf m s)) ∩
    g.trim m (g.tubeOf m s) (g.ballOf m s)

/-- Every retained piece lies in its original tube. -/
theorem ConcreteTubeBallGeometry.piece_subset_tube
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    g.piece m s ⊆ tubes (g.tubeOf m s) := by
  intro x hx
  exact hx.1.1.1.1

/-- Every retained piece belongs to the greedy gain of its parent. -/
theorem ConcreteTubeBallGeometry.piece_subset_gain
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    g.piece m s ⊆ g.gain m (g.tubeOf m s) := by
  intro x hx
  exact hx.1.1.1.2

/-- Every retained piece lies in the original dyadic level. -/
theorem ConcreteTubeBallGeometry.piece_subset_level
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    g.piece m s ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m := by
  intro x hx
  exact hx.1.1.2

/-- Every retained piece lies in the ball specified by its label. -/
theorem ConcreteTubeBallGeometry.piece_subset_ball
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    g.piece m s ⊆ g.ball m (g.ballOf m s) := by
  intro x hx
  exact hx.1.2

/-- The greedy gains of distinct selected tubes are disjoint. -/
theorem ConcreteTubeBallGeometry.gain_disjoint
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i j : T) (hij : i ≠ j) :
    Disjoint (g.gain m i) (g.gain m j) := by
  by_cases hi : i ∈ g.B m
  · by_cases hj : j ∈ g.B m
    · have hd := Kakeya.Eighty9.selected_gain_disjoint_of_order
        tubes (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.B m) (g.chosen m) (g.stage m) (g.hChosen m)
        i hi j hj hij
      simpa [ConcreteTubeBallGeometry.gain, hi, hj] using hd
    · simp [ConcreteTubeBallGeometry.gain, hi, hj]
  · simp [ConcreteTubeBallGeometry.gain, hi]

/-- Measurability follows from the tube, gain, ball, and trimming sets. -/
theorem ConcreteTubeBallGeometry.piece_measurable
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hBall : ∀ m i, MeasurableSet (g.ball m i))
    (hTrim : ∀ m j i, MeasurableSet (g.trim m j i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m}) :
    MeasurableSet (g.piece m s) := by
  have hBand : MeasurableSet (Kakeya.Eighty4.concreteDyadicBand tubes m) :=
    Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m
  have hGain : MeasurableSet (g.gain m (g.tubeOf m s)) := by
    by_cases hj : g.tubeOf m s ∈ g.B m
    · simpa [ConcreteTubeBallGeometry.gain, hj] using
        (Kakeya.Eighty4.concreteGreedyGain_measurable
          tubes (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (g.chosen m) hBand hT (g.stage m (g.tubeOf m s)))
    · simp [ConcreteTubeBallGeometry.gain, hj]
  exact ((((hT (g.tubeOf m s)).inter hGain).inter hBand).inter
    (hBall m (g.ballOf m s))).inter (hTrim m (g.tubeOf m s) (g.ballOf m s))

/-- The analytic and Vitali bounds used with the concrete retained construction. -/
structure ConcreteTubeBallBounds
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes) where
  hNonempty : ∀ m s, (g.piece m s).Nonempty
  hBallOccupied : ∀ m i,
    (g.ball m i ∩ Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty
  C : ℝ
  A : ℝ
  deltaPow : ℝ
  Z : ℝ
  ballPackingConstant : ℝ
  hC : 0 ≤ C
  hA : 0 ≤ A
  hDeltaPow : 0 ≤ deltaPow
  hScaleLe : ∀ m,
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤ (Fintype.card T : ℝ)
  hSelectedCard : ∀ m, (g.B m).card ≤
    ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊
  hVolume : ∀ m s,
    Kakeya.Conditional.mass μ (g.piece m s) ≤ C * deltaPow *
      (A * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / ((n : ℝ) - 1))))
  hNormalization : (Fintype.card T : ℝ) * deltaPow ≤ Z
  hBallPackingConstant : 0 ≤ ballPackingConstant
  hHallRight : ∀ m r,
    (∑ i : Fin (g.ballCount m),
      if (g.ball m i ∩ tubes r).Nonempty then (1 : ℝ) else 0) ≤
      ballPackingConstant * (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        ((1 : ℝ) / ((n : ℝ) - 1))

/-- Build the retained dyadic data from the actual trimmed tube–ball intersections. -/
noncomputable def ConcreteTubeBallGeometry.toBallLocalized
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X) (n : ℕ)
    (b : ConcreteTubeBallBounds μ tubes n g) :
    BallLocalizedDyadicData (K := T × ℕ) μ tubes n := by
  classical
  exact {
    B := g.B
    P := g.P
    retainedPiece := g.piece
    gain := g.gain
    parent := fun _ p => p.val.1
    hParent := by
      intro m p
      exact g.hPSelected m p.val p.property
    hGainDisjoint := g.gain_disjoint
    hNonempty := b.hNonempty
    hTrimmed := by
      intro m p x hx
      have hTube : x ∈ tubes p.val.1 := g.piece_subset_tube m (Sum.inr p) hx
      have hGain : x ∈ g.gain m p.val.1 :=
        g.piece_subset_gain m (Sum.inr p) hx
      exact ⟨hTube, hGain⟩
    hLevel := g.piece_subset_level
    radius := fun m => b.A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / ((n : ℝ) - 1)))
    C := b.C
    deltaPow := b.deltaPow
    Z := b.Z
    radiusCap := b.A
    hC := b.hC
    hDeltaPow := b.hDeltaPow
    hRadiusNonneg := by
      intro m
      exact Kakeya.Eighty9.canonical_dyadic_radius_nonneg
        n (Fintype.card T) b.A b.hA m
    hGreedy := by
      intro m
      exact Kakeya.Eighty9.greedy_selected_card_budget (g.B m)
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
        (Fintype.card T : ℝ)
        (Kakeya.Eighty4.dyadicScale_pos _ m)
        (b.hScaleLe m) (b.hSelectedCard m)
    hVolume := b.hVolume
    hNormalization := b.hNormalization
    hRadiusScale := by
      intro m
      exact le_of_eq (Kakeya.Eighty9.canonical_dyadic_radius_scale
        n (Fintype.card T) b.A m)
    ballCount := g.ballCount
    ball := g.ball
    sourceBall := g.ballOf
    hSourceBall := g.piece_subset_ball
    hBallOccupied := b.hBallOccupied
    ballPackingConstant := b.ballPackingConstant
    hBallPackingConstant := b.hBallPackingConstant
    hHallRight := b.hHallRight
  }

/-- Tube–ball pair indexing is automatic for this concrete construction. -/
theorem ConcreteTubeBallGeometry.pairIndexing
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X) (n : ℕ)
    (b : ConcreteTubeBallBounds μ tubes n g) :
    TubeBallPairIndexing μ tubes n (g.toBallLocalized μ n b) := by
  constructor
  · intro m p
    rfl
  · intro m p
    rfl

/-- The regular-piece budget follows from the concrete pair labels at the cutoff. -/
noncomputable def ConcreteTubeBallGeometry.paper46Construction
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X) (n : ℕ) (hn : 3 ≤ n)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hq : paper46Cutoff b.ballPackingConstant ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Paper46ConstructionData μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData m :=
  paper46Construction_of_pair_indexing_at_cutoff
    μ tubes n hn (g.toBallLocalized μ n b)
    (g.pairIndexing μ n b) m hq

/-- Greedy capture data for the original greedy gains and the retained family. -/
structure ConcreteTubeBallGreedy
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes) where
  hScaleLe : ∀ m, Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
    (Fintype.card T : ℝ)
  hStep : ∀ m k,
    Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (g.greedyQ m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m / (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (g.greedyQ m) k
  hCover : ∀ m, Kakeya.Eighty4.greedyUnion (g.greedyQ m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ p, g.piece m p
  hT : ∀ j, MeasurableSet (tubes j)
  hBall : ∀ m i, MeasurableSet (g.ball m i)
  hTrim : ∀ m j i, MeasurableSet (g.trim m j i)

/-- The ordered greedy gains have a measurable union contained in the dyadic level. -/
theorem ConcreteTubeBallGeometry.greedyQ_measurable
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (hT : ∀ j, MeasurableSet (tubes j))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    MeasurableSet (g.greedyQ m k) := by
  exact Kakeya.Eighty4.concreteGreedyGain_measurable tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.chosen m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m) hT k

theorem ConcreteTubeBallGeometry.greedyQ_subset_level
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    g.greedyQ m k ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m :=
  Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.chosen m) k

/-- Transfer greedy capture from the actual greedy gains and tube–ball pieces. -/
noncomputable def ConcreteTubeBallGreedy.toRetainedGreedy
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTubeBallGreedy μ tubes n g) :
    RetainedGreedyAtLevels μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData := by
  exact {
    Q := g.greedyQ
    hScaleLe := c.hScaleLe
    hUnionMeasurable := by
      intro m
      exact Kakeya.Eighty4.greedyUnion_measurable (g.greedyQ m)
        (g.greedyQ_measurable c.hT m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊
    hUnionSubset := by
      intro m x hx
      change x ∈ ⋃ k ∈ Finset.range
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
        g.greedyQ m k at hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_, hkx⟩ := Set.mem_iUnion.mp hk
      exact g.greedyQ_subset_level m k hkx
    hStep := c.hStep
    hPieceMeasurable := by
      intro m p
      exact g.piece_measurable c.hT c.hBall c.hTrim m p
    hCover := c.hCover
  }

end Kakeya.Ninety21
