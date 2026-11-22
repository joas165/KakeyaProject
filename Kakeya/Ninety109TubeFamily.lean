module

public import Kakeya.Ninety109RetainedCover

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal

theorem isCompact_unitTube {n : ℕ} (p u : Space n) (δ : ℝ) : IsCompact (unitTube p u δ) := by
  let W := Metric.closedBall (0 : Space n) δ ∩ {w | inner ℝ w u = 0}
  have hW : IsCompact W := (isCompact_closedBall _ _).inter_right
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  let F := fun z : ℝ × Space n => p + z.1 • u + z.2
  have hc : Continuous F :=
    (continuous_const.add (continuous_fst.smul continuous_const)).add continuous_snd
  have h := (isCompact_Icc (α := ℝ) (a := -(1 / 2)) (b := 1 / 2)).prod hW
  have he : unitTube p u δ = F '' (Set.Icc (-(1 / 2)) (1 / 2) ×ˢ W) := by
    ext x
    constructor
    · rintro ⟨t, w, ht, hw, hδ, rfl⟩
      exact ⟨(t, w), ⟨abs_le.mp ht, (by simpa using hδ : w ∈ Metric.closedBall 0 δ), hw⟩, rfl⟩
    · rintro ⟨⟨t, w⟩,⟨ht, hδ, hw⟩, rfl⟩
      exact ⟨t, w, abs_le.mpr ht, hw, by simpa using hδ, rfl⟩
  rw [he]
  exact h.image hc

variable {T : Type*} [Fintype T] [Nonempty T] {d : ℕ}

structure TubeFamily (T : Type*) [Fintype T] (d : ℕ) (A : ℝ≥0) where
  center : T → Space (d + 2)
  direction : T → Space (d + 2)
  δ : ℝ
  positive : 0 < δ
  unit : ∀ i, ‖direction i‖ = 1
  separated : ∀ i j, i ≠ j → δ ≤ dist (direction i) (direction j)
  scale : δ * (Fintype.card T : ℝ) ^ ((1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) ≤ A

variable {A : ℝ≥0} (f : TubeFamily T d A)

namespace TubeFamily

abbrev tube (i : T) := unitTube (f.center i) (f.direction i) f.δ

omit [Nonempty T] in
theorem measurable (i : T) : MeasurableSet (f.tube i) :=
  (isCompact_unitTube _ _ _).isClosed.measurableSet

omit [Nonempty T] in
theorem bounded (m) : Bornology.IsBounded (concreteDyadicBand f.tube m) := by
  classical
  apply (Bornology.isBounded_iUnion.mpr (fun i : T => (isCompact_unitTube
    (f.center i) (f.direction i) f.δ).isBounded)).subset
  intro x hx
  by_contra hn
  have hnone : ∀ i, x ∉ f.tube i := by simpa using hn
  have h := hx.1
  rw [tubeMultiplicity_eq_count] at h
  exact (dyadicScale_pos _ m).not_ge (by simpa [finiteTubeCount, hnone] using h)

include f in
theorem A_pos : 0 < (A : ℝ) :=
  (mul_pos f.positive (Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (Fintype.card_pos (α := T))) _)).trans_le f.scale

omit [Nonempty T] in
theorem normalization : (Fintype.card T : ℝ) * f.δ ^ (d + 1) ≤ (A : ℝ) ^ (d + 1) := by
  have h := pow_le_pow_left₀ (mul_nonneg f.positive.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    f.scale (d + 1)
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)] at h
  have he : (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1) * ((d + 1 : ℕ) : ℝ) = 1 := by
    push_cast
    rw [show (d : ℝ) + 2 - 1 = d + 1 by ring]
    field_simp
  simpa only [he, Real.rpow_one, mul_comm] using h

variable (μ : Measure (Space (d + 2))) [IsFiniteMeasure μ]

noncomputable abbrev candidates :=
  ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains μ f.tube
    (canonicalGreedyVitaliRadius (T := T) (d + 2) A)
    (canonicalGreedyVitaliRadius_pos (T := T) (d + 2) A f.A_pos) f.bounded

noncomputable def volumeCoefficient (d : ℕ) := 6 * tripleRadiusTransverseCoefficient d

theorem coefficient_bounds :
    0 ≤ volumeCoefficient d ∧ 2 * tripleRadiusTransverseCoefficient d ≤ volumeCoefficient d := by
  have h : 0 ≤ tripleRadiusTransverseCoefficient d := ENNReal.toReal_nonneg
  unfold volumeCoefficient
  constructor <;> linarith

variable (hμ : μ ≤ volume)

noncomputable abbrev bounds :=
  ConcreteGreedyVitaliCandidates.euclideanBoundsOfCompactMaximalUnusedGeometry
    μ f.center f.direction f.δ f.positive.le f.measurable f.unit hμ
    A (volumeCoefficient d) ((A : ℝ) ^ (d + 1)) f.A_pos coefficient_bounds.1 coefficient_bounds.2
    f.scale f.bounded f.normalization

theorem piece_volume : CoverVolumeBound (f.candidates μ) μ (f.bounds μ hμ) := by
  intro m a
  let v := f.candidates μ
  let b := f.bounds μ hμ
  let j := v.retained.tubeOf m a
  let i := v.retained.ballOf m a
  have hR (l) : v.radius l = twoRadiusRadius v.retained b l := rfl
  have h := v.euclidean_triple_cost μ f.center f.direction f.δ f.positive.le _ b
    f.measurable (fun j hj => by simpa [hj] using f.unit j) hμ hR rfl le_rfl m j i
  have hsub : coverPiece v m a ⊆ f.tube j ∩ Metric.ball (v.centers m i) (3 * v.radius m) :=
    Set.inter_subset_inter_left _ (v.retained.gain_subset_parentTube m j)
  have hle := measure_mono (μ := μ) hsub
  rw [conditional_mass_eq_measure_toReal μ _
    ((f.measurable j).inter Metric.isOpen_ball.measurableSet)] at h
  rw [conditional_mass_eq_measure_toReal μ _ (coverPiece_measurable v f.measurable m a)]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hle).trans h

noncomputable abbrev retained := coverData (f.candidates μ) μ (f.bounds μ hμ) (f.piece_volume μ hμ)

noncomputable def greedy : RetainedGreedyAtLevels μ f.tube (d + 2) (f.retained μ hμ) := by
  apply coverGreedy
  exact ConcreteTwoRadiusGreedy.ofCompactMaximalUnusedGeometry μ f.center f.direction f.δ
    f.positive.le f.measurable f.unit hμ A (volumeCoefficient d) ((A : ℝ) ^ (d + 1)) f.A_pos
    coefficient_bounds.1 coefficient_bounds.2 le_rfl f.scale f.bounded f.normalization

end TubeFamily
end Kakeya.Ninety109
