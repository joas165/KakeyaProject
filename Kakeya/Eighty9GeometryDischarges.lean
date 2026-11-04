module
public import Kakeya.Eighty9FullConditionalFromLowerIncidence
public import Kakeya.Eighty9GreedyGain
public import Kakeya.Eighty9FiniteVitali
public import Kakeya.Eighty9VitaliFiberBridge
public import Kakeya.Eighty9GreedyCover
public import Kakeya.Eighty5TubeBallVolume

/-!
# Geometric hypotheses: constructive reductions

This file does NOT assume or prove `LowerIncidence`.

The following facts are derived from explicit upstream data:
* greedy gain disjointness, if gains are defined by an ordered greedy sequence;
* radius-scale equality for the canonical dyadic radius;
* per-tube finite Vitali balls, disjointness, triple-radius coverage,
  nonempty fibers and nonempty selected intersections;
* transport of an ORIGINAL localized greedy-union cover to the SELECTED
  triple-radius Vitali cover.

The original localized cover, the greedy recurrence, the direction-packing
normalization, and the arbitrary-orientation Euclidean coordinate frame are
separate geometric tasks. We do not silently convert them into theorems.
-/

@[expose] public section

namespace Kakeya.Eighty9

open MeasureTheory

/-- Disjointness of greedy gains for distinct original selected tubes follows
from their distinct positions in the chosen tube ordering. -/
theorem selected_gain_disjoint_of_order
    {X T : Type*} (tubes : T → Set X) (F : Set X)
    (B : Finset T) (chosen : ℕ → T) (stage : T → ℕ)
    (hChosen : ∀ j ∈ B, chosen (stage j) = j) :
    ∀ j ∈ B, ∀ j' ∈ B, j ≠ j' →
      Disjoint
        (Kakeya.Eighty4.concreteGreedyGain tubes F chosen (stage j))
        (Kakeya.Eighty4.concreteGreedyGain tubes F chosen (stage j')) := by
  intro j hj j' hj' hne
  have hstage : stage j ≠ stage j' := by
    intro h
    apply hne
    calc
      j = chosen (stage j) := (hChosen j hj).symm
      _ = chosen (stage j') := by rw [h]
      _ = j' := hChosen j' hj'
  rcases lt_or_gt_of_ne hstage with hlt | hgt
  · exact Kakeya.Eighty4.concreteGreedyGain_disjoint tubes F chosen hlt
  · exact (Kakeya.Eighty4.concreteGreedyGain_disjoint tubes F chosen hgt).symm

/-- Purely algebraic dyadic-radius relation; no geometric hypothesis. -/
theorem exact_radius_scale (q a C : ℝ) (hq : 0 < q) :
    q ^ a * (C * q ^ (-a)) = C := by
  have hpow : q ^ a * q ^ (-a) = 1 := by
    rw [← Real.rpow_add hq]
    simp
  calc
    q ^ a * (C * q ^ (-a)) = C * (q ^ a * q ^ (-a)) := by ring
    _ = C := by rw [hpow, mul_one]

/-- The precise canonical dyadic radius satisfies the level-scale bound
with equality. -/
theorem canonical_dyadic_radius_scale
    (n N : ℕ) (C : ℝ) (m : Kakeya.Eighty4.DyadicIndex N) :
    (Kakeya.Eighty4.dyadicScale N m) ^
        ((1 : ℝ) / ((n : ℝ) - 1)) *
      (C * (Kakeya.Eighty4.dyadicScale N m) ^
        (-((1 : ℝ) / ((n : ℝ) - 1)))) = C := by
  exact exact_radius_scale _ _ C
    (Kakeya.Eighty4.dyadicScale_pos N m)

/-- The canonical radius is nonnegative for nonnegative C. -/
theorem canonical_dyadic_radius_nonneg
    (n N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (m : Kakeya.Eighty4.DyadicIndex N) :
    0 ≤ C * (Kakeya.Eighty4.dyadicScale N m) ^
      (-((1 : ℝ) / ((n : ℝ) - 1))) := by
  exact mul_nonneg hC
    (Real.rpow_nonneg (Kakeya.Eighty4.dyadicScale_pos N m).le _)

/-- Selecting Vitali subfamilies of NONEMPTY original localized pieces
provides the disjointness, nonempty fibers and selected-piece nonemptiness
simultaneously. None of these is a new independent geometry axiom. -/
theorem exists_vitali_with_nonempty_localized_pieces
    {T I X : Type*} [MetricSpace X]
    (B : Finset T) (L : T → Finset I)
    (b : T → I → X) (R : ℝ) (hR : 0 < R)
    (tube gain : T → Set X) (F : Set X)
    (hL : ∀ j ∈ B, (L j).Nonempty)
    (hOriginal : ∀ j ∈ B, ∀ i ∈ L j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    ∃ S : T → Finset I,
      (∀ j ∈ B, S j ⊆ L j) ∧
      (∀ j ∈ B, (S j).Nonempty) ∧
      (∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (Metric.ball (b j i) R) (Metric.ball (b j i') R)) ∧
      (∀ j ∈ B, ∀ i ∈ S j,
        ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) ∧
      (∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
        Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) := by
  obtain ⟨S, hSub, hBalls, hCover⟩ :=
    exists_tubeWise_equal_radius_vitali B L b R hR
  refine ⟨S, hSub, ?_, hBalls, ?_, hCover⟩
  · exact tubeWise_vitali_nonempty_fibers B L S b R hL hCover
  · exact chosen_small_piece_nonempty_of_vitali_subfamily
      tube gain F b R B L S hSub hOriginal

/-- The original localized cover implies a cover by the enlarged balls
chosen by Vitali. This does NOT assert that the original localized
cover itself follows from greedy selection without geometry. -/
theorem localized_cover_transfers_to_vitali
    {T I X : Type*} [MetricSpace X]
    (B : Finset T) (L S : T → Finset I)
    (tube gain : T → Set X) (F U : Set X)
    (b : T → I → X) (R : ℝ)
    (hOriginalCover :
      U ⊆ ⋃ j ∈ B, ⋃ i ∈ L j,
        (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R))
    (hVitaliCover : ∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
      Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) :
    U ⊆ ⋃ j ∈ B, ⋃ d ∈ S j,
      (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j d) (3 * R)) := by
  intro x hx
  have hxCover := hOriginalCover hx
  simp only [Set.mem_iUnion] at hxCover ⊢
  obtain ⟨j, hj, i, hi, hxi⟩ := hxCover
  obtain ⟨d, hd, hball⟩ := hVitaliCover j hj i hi
  exact ⟨j, hj, d, hd, ⟨hxi.1, hball hxi.2⟩⟩

/-- A greedy bound for any selected subset with at most `ceil(N/q)` tubes.
This discharges `hGreedy` from the ordinary greedy cardinality budget. -/
theorem greedy_selected_card_budget
    {T : Type*} (B : Finset T)
    (q N : ℝ) (hq : 0 < q) (hqN : q ≤ N)
    (hB : B.card ≤ ⌈N / q⌉₊) :
    q * (B.card : ℝ) ≤ 2 * N := by
  have hcap := (Kakeya.Eighty4.greedy_ceiling_budget q N hq hqN).2
  have hcard : (B.card : ℝ) ≤ (⌈N / q⌉₊ : ℝ) := by
    exact_mod_cast hB
  exact (mul_le_mul_of_nonneg_left hcard hq.le).trans hcap


/-- Upgrade the INITIAL localized cover to a genuine major-portion
mass-capture inequality for the ACTUAL selected triple-radius pieces.
This uses the proved finite Vitali covering lemma; it does not assume
mass capture as a separate black-box inequality. The initial localization
of the greedy union and the greedy residual recurrence are premises. -/
theorem mass_capture_of_original_localized_greedy_cover
    {X T I : Type*} [MetricSpace X] [MeasurableSpace X]
    [Fintype T] [DecidableEq T] [DecidableEq I]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set X) (Q : ℕ → Set X)
    (B : Finset T) (L S : T → Finset I)
    (tube gain : T → Set X) (b : T → I → X) (R : ℝ)
    (q N : ℝ) (hq : 0 < q) (hqN : q ≤ N)
    (hF : MeasurableSet F)
    (hU : MeasurableSet (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊))
    (hSub : Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊ ⊆ F)
    (hStep : ∀ k,
      Kakeya.Eighty4.greedyResidual μ F Q (k + 1) ≤
        (1 - q / N) * Kakeya.Eighty4.greedyResidual μ F Q k)
    (hOriginalCover :
      Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊ ⊆
        ⋃ j ∈ B, ⋃ i ∈ L j,
          (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R))
    (hVitaliCover : ∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
      Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R))
    (hMeasurable : ∀ j ∈ B, ∀ d ∈ S j,
      MeasurableSet
        (((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j d) (3 * R))) :
    Kakeya.Conditional.mass μ F ≤
      (1 / (1 - Real.exp (-1))) *
        (∑ p : TubeWiseVitaliLabel B S,
          Kakeya.Conditional.mass μ
            (((tube p.1.val ∩ gain p.1.val) ∩ F) ∩
              Metric.ball (b p.1.val p.2.val) (3 * R))) := by
  classical
  let E : TubeWiseVitaliLabel B S → Set X := fun p =>
    (((tube p.1.val ∩ gain p.1.val) ∩ F) ∩
      Metric.ball (b p.1.val p.2.val) (3 * R))
  let G : TubeWiseVitaliLabel B S → Set X := fun _ => Set.univ
  have hPieces : ∀ p ∈ (Finset.univ : Finset (TubeWiseVitaliLabel B S)),
      MeasurableSet (E p ∩ G p) := by
    intro p _
    simpa [E, G] using
      hMeasurable p.1.val p.1.property p.2.val p.2.property
  have hTransfer := localized_cover_transfers_to_vitali
    B L S tube gain F
      (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊)
      b R hOriginalCover hVitaliCover
  have hCovered : Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊ ⊆
      ⋃ p ∈ (Finset.univ : Finset (TubeWiseVitaliLabel B S)), E p ∩ G p := by
    intro x hx
    have hxCover := hTransfer hx
    simp only [Set.mem_iUnion] at hxCover ⊢
    obtain ⟨j, hj, d, hd, hxPiece⟩ := hxCover
    let p : TubeWiseVitaliLabel B S := ⟨⟨j, hj⟩, ⟨d, hd⟩⟩
    refine ⟨p, Finset.mem_univ _, ?_⟩
    exact ⟨hxPiece, Set.mem_univ x⟩
  have hCapture := Kakeya.Eighty4.mass_capture_from_greedy_union
    μ F Q E G (Finset.univ : Finset (TubeWiseVitaliLabel B S))
    q N hq hqN hF hU hSub hStep hPieces hCovered
  simpa [E, G] using hCapture

/-- An exact normalization for the model parameter δ^(n-1) := 1/N.
This is NOT a proof of packing for arbitrary δ-separated directions. -/
theorem algebraic_unit_normalization
    (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (1 / (N : ℝ)) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hn]

end Kakeya.Eighty9

namespace Kakeya.Eighty9

open MeasureTheory

/-- A further localized piece restriction cannot increase its volume.
This explicitly links the actual gain/dyadic intersections to the
straightened-coordinate tube-ball lemma, subject to the frame bridge. -/
theorem localized_unitTube_ball_volume_le_of_frame
    (k : ℕ)
    (p v b : Kakeya.Space (k + 2)) (δ R : ℝ)
    (gain F : Set (Kakeya.Space (k + 2)))
    (coords : Kakeya.Space (k + 2) → Kakeya.TubeBall.Axial k)
    (hcoords : MeasurePreserving coords
      (volume : Measure (Kakeya.Space (k + 2))) volume)
    (transverseCenter : Kakeya.TubeBall.Transverse k)
    (c : Kakeya.TubeBall.Axial k)
    (hTube : Kakeya.unitTube p v δ ⊆
      coords ⁻¹' Kakeya.TubeBall.straightTube k transverseCenter δ)
    (hBall : Metric.closedBall b R ⊆
      coords ⁻¹' Metric.closedBall c R) :
    (volume : Measure (Kakeya.Space (k + 2)))
      ((((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩
        Metric.ball b R)) ≤
      ENNReal.ofReal (2 * R) *
        (volume : Measure (Kakeya.TubeBall.Transverse k))
          (Metric.closedBall transverseCenter δ) := by
  have hsub :
      (((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩ Metric.ball b R) ⊆
        Kakeya.unitTube p v δ ∩ Metric.closedBall b R := by
    intro x hx
    exact ⟨hx.1.1.1, Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hx.2))⟩
  exact (measure_mono hsub).trans
    (Kakeya.TubeBall.unitTube_ball_volume_le_of_frame
      k p v b δ R coords hcoords transverseCenter c hTube hBall)

end Kakeya.Eighty9
