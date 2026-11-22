module

public import Kakeya.Ninety109RegularPieceCount
public import Kakeya.Ninety21ExceptionalPerLevelEndpoint

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21

variable {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (v : ConcreteGreedyVitaliCandidates tubes g)

abbrev CoverLabel (m : DyadicIndex (Fintype.card T)) :=
  {j // j ∈ v.retained.B m} ⊕ {p // p ∈ v.retained.P m}

def coverPiece (m : DyadicIndex (Fintype.card T)) (p : CoverLabel v m) : Set X :=
  v.retained.gain m (v.retained.tubeOf m p) ∩
    Metric.ball (v.centers m (v.retained.ballOf m p)) (3 * v.radius m)

omit [BorelSpace X] in
theorem coverPiece_nonempty (m) (p : CoverLabel v m) : (coverPiece v m p).Nonempty := by
  obtain ⟨x, hx⟩ := v.retained_piece_nonempty m p
  have hb := v.retained.piece_subset_ball m p hx
  change x ∈ g.ball m (v.retained.ballOf m p) at hb
  rw [v.hBall m (v.retained.ballOf m p)] at hb
  exact ⟨x, v.retained.piece_subset_gain m p hx,
    Metric.ball_subset_ball (by linarith [v.hRadius m]) hb⟩

theorem coverPiece_measurable (hT : ∀ j, MeasurableSet (tubes j)) (m) (p : CoverLabel v m) :
    MeasurableSet (coverPiece v m p) := by
  apply MeasurableSet.inter _ Metric.isOpen_ball.measurableSet
  unfold ConcreteTubeBallGeometry.gain
  split
  · exact v.retained.greedyQ_measurable hT m _
  · exact MeasurableSet.empty

omit [BorelSpace X] in
theorem greedyUnion_subset_coverPieces (m) :
    greedyUnion (v.retained.greedyQ m)
      ⌈(Fintype.card T : ℝ) / dyadicScale (Fintype.card T) m⌉₊ ⊆ ⋃ p, coverPiece v m p := by
  classical
  have h := g.occupiedVitali_cover_transfer v.selected m
    (fun j i => g.gain m j ∩ Metric.ball (v.centers m i) (3 * v.radius m)) _
    (v.selected_occupied m) (Classical.choose_spec (v.exists_selected_gain m)).2.2.2
  intro x hx
  rw [v.retained_greedyQ_eq] at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (h hx)
  obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hiS
  have ht := (Finset.mem_filter.mp hp).2
  apply Set.mem_iUnion.mpr
  refine ⟨p, ?_⟩
  change (v.retained.gain m (v.retained.tubeOf m p) ∩
    Metric.ball (v.centers m (v.retained.ballOf m p)) (3 * v.radius m)) x
  rw [show v.retained.tubeOf m p = j from ht, show v.retained.ballOf m p = i from he]
  have hg : v.retained.gain m j = g.gain m j := g.occupiedVitali_gain_eq v.selected m j hjB
  rw [hg]
  exact hxi

variable {n : ℕ} (μ : Measure X) [IsFiniteMeasure μ]
    (b : ConcreteTubeBallBounds μ tubes n v.retained)

def CoverVolumeBound : Prop :=
  ∀ m (p : CoverLabel v m), Conditional.mass μ (coverPiece v m p) ≤
    b.C * b.deltaPow * twoRadiusRadius v.retained b m

noncomputable def coverData (hv : CoverVolumeBound v μ b) :
    RetainedDyadicData (K := T × ℕ) μ tubes n :=
  { (v.retained.toBallLocalized μ n b).toRetainedDyadicData with
    retainedPiece := coverPiece v
    hNonempty := coverPiece_nonempty v
    hTrimmed := fun m _p _ hx =>
      ⟨v.retained.gain_subset_parentTube m _ hx.1, hx.1⟩
    hLevel := fun m _p _ hx => v.retained.gain_subset_dyadicLevel m _ hx.1
    hVolume := hv }

noncomputable def coverGreedy (hv : CoverVolumeBound v μ b)
    (c : ConcreteTwoRadiusGreedy μ tubes n v.retained b) :
    RetainedGreedyAtLevels μ tubes n (coverData v μ b hv) where
  Q := v.retained.greedyQ
  hScaleLe := b.hScaleLe
  hUnionMeasurable := fun m => greedyUnion_measurable _ (v.retained.greedyQ_measurable c.hT m) _
  hUnionSubset := by
    intro m x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_, hxk⟩ := Set.mem_iUnion.mp hk
    exact v.retained.greedyQ_subset_level m k hxk
  hStep := c.hStep
  hPieceMeasurable := coverPiece_measurable v c.hT
  hCover := greedyUnion_subset_coverPieces v

end Kakeya.Ninety109
