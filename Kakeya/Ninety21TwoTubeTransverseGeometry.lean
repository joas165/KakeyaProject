module

public import Kakeya.Ninety21OriginalTubeBallPacking

/-!
# Two-tube transverse localization geometry

A ball meeting a Euclidean tube has its center within `R + δ` of an axis
point. Uniform transversality controls the distance between centers of balls
meeting both tubes. These estimates use the original geometric tubes.
-/

@[expose] public section

namespace Kakeya.Ninety21

/-- The center of a radius-`R` ball meeting a `δ`-tube lies within
`R + δ` of a point on its central segment. -/
theorem originalTube_ball_center_near_axis
    {n : ℕ} (p v b : Kakeya.Space n) (δ R : ℝ)
    (hHit : (Metric.ball b R ∩ Kakeya.unitTube p v δ).Nonempty) :
    ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧
      dist b (p + t • v) ≤ R + δ := by
  obtain ⟨x, hxb, hxt⟩ := hHit
  obtain ⟨t, w, ht, _hw, hnorm, hx⟩ := hxt
  subst x
  refine ⟨t, ht, ?_⟩
  have hball : dist b (p + t • v + w) < R := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hxb)
  have hshift : dist (p + t • v + w) (p + t • v) ≤ δ := by
    have heq : (p + t • v + w) - (p + t • v) = w := by abel
    simpa only [dist_eq_norm, heq] using hnorm
  have htri := dist_triangle b (p + t • v + w) (p + t • v)
  linarith

/-- Quantitative separation of two line directions. -/
def TransverseDirections {n : ℕ}
    (u v : Kakeya.Space n) (θ : ℝ) : Prop :=
  ∀ a b : ℝ, θ * |a| ≤ ‖a • u - b • v‖

/-- Centers of two balls meeting both transverse tubes are close at scale
`R`, independently of the distance between the translated tube axes. -/
theorem two_transverse_tubes_ball_center_diameter
    {n : ℕ} (p q u v b b' : Kakeya.Space n) (δ R θ : ℝ)
    (hθ : 0 < θ) (hδR : δ ≤ R) (hu : ‖u‖ = 1)
    (hTrans : TransverseDirections u v θ)
    (hbP : (Metric.ball b R ∩ Kakeya.unitTube p u δ).Nonempty)
    (hbQ : (Metric.ball b R ∩ Kakeya.unitTube q v δ).Nonempty)
    (hb'P : (Metric.ball b' R ∩ Kakeya.unitTube p u δ).Nonempty)
    (hb'Q : (Metric.ball b' R ∩ Kakeya.unitTube q v δ).Nonempty) :
    dist b b' ≤ (4 + 8 / θ) * R := by
  obtain ⟨a, _ha, ha⟩ := originalTube_ball_center_near_axis p u b δ R hbP
  obtain ⟨c, _hc, hc⟩ := originalTube_ball_center_near_axis q v b δ R hbQ
  obtain ⟨a', _ha', ha'⟩ := originalTube_ball_center_near_axis p u b' δ R hb'P
  obtain ⟨c', _hc', hc'⟩ := originalTube_ball_center_near_axis q v b' δ R hb'Q
  let P : Kakeya.Space n := p + a • u
  let P' : Kakeya.Space n := p + a' • u
  let Q : Kakeya.Space n := q + c • v
  let Q' : Kakeya.Space n := q + c' • v
  have hPQ : ‖P - Q‖ ≤ 2 * (R + δ) := by
    have ht := dist_triangle P b Q
    have ha0 : dist P b ≤ R + δ := by simpa only [dist_comm] using ha
    have hc0 : dist b Q ≤ R + δ := hc
    have hdist : dist P Q ≤ 2 * (R + δ) := by linarith
    simpa only [dist_eq_norm] using hdist
  have hP'Q' : ‖P' - Q'‖ ≤ 2 * (R + δ) := by
    have ht := dist_triangle P' b' Q'
    have ha0 : dist P' b' ≤ R + δ := by simpa only [dist_comm] using ha'
    have hc0 : dist b' Q' ≤ R + δ := hc'
    have hdist : dist P' Q' ≤ 2 * (R + δ) := by linarith
    simpa only [dist_eq_norm] using hdist
  have hVector : (a - a') • u - (c - c') • v =
      (P - Q) - (P' - Q') := by
    dsimp [P, P', Q, Q']
    rw [sub_smul, sub_smul]
    abel
  have hDifference : ‖(a - a') • u - (c - c') • v‖ ≤
      4 * (R + δ) := by
    rw [hVector]
    calc
      ‖(P - Q) - (P' - Q')‖ ≤ ‖P - Q‖ + ‖P' - Q'‖ := norm_sub_le _ _
      _ ≤ 4 * (R + δ) := by linarith
  have hAngle := hTrans (a - a') (c - c')
  have hAxis : |a - a'| ≤ 4 * (R + δ) / θ := by
    apply (le_div_iff₀ hθ).2
    nlinarith
  have hAxisDist : dist P P' = |a - a'| := by
    have hEq : P - P' = (a - a') • u := by
      dsimp [P, P']
      rw [sub_smul]
      abel
    rw [dist_eq_norm, hEq, norm_smul, hu]
    simp
  have hBB : dist b b' ≤ 2 * (R + δ) + |a - a'| := by
    have ht1 := dist_triangle b P b'
    have ht2 := dist_triangle P P' b'
    have hbP' : dist P' b' ≤ R + δ := by simpa only [dist_comm] using ha'
    rw [hAxisDist] at ht2
    linarith
  have hδ : R + δ ≤ 2 * R := by linarith
  have hScaled : 4 * (R + δ) / θ ≤ 8 * R / θ := by
    have hn : 4 * (R + δ) ≤ 8 * R := by linarith
    have hp := mul_le_mul_of_nonneg_right hn hθ.le
    exact (div_le_div_iff₀ hθ hθ).2 (by nlinarith)
  have hEnd : dist b b' ≤ 4 * R + 8 * R / θ := by
    linarith
  calc
    dist b b' ≤ 4 * R + 8 * R / θ := hEnd
    _ = (4 + 8 / θ) * R := by ring


/-- A radius-`R/2` net bounds the cardinality of a disjoint family of
radius-`R` balls. -/
theorem disjoint_balls_card_le_half_radius_net
    {X I : Type*} [MetricSpace X]
    (centers : I → X) (R : ℝ) (hR : 0 < R)
    (J : Finset I) (Z : Finset X)
    (hDisjoint : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (Metric.ball (centers i) R) (Metric.ball (centers j) R))
    (hNet : ∀ i ∈ J, ∃ z ∈ Z, dist (centers i) z < R / 2) :
    J.card ≤ Z.card := by
  classical
  let pick : {i : I // i ∈ J} → {z : X // z ∈ Z} :=
    fun i => ⟨Classical.choose (hNet i.val i.property),
      (Classical.choose_spec (hNet i.val i.property)).1⟩
  have hpick : Function.Injective pick := by
    intro i j heq
    apply Subtype.ext
    by_contra hij
    have hz : (pick i).val = (pick j).val := congrArg Subtype.val heq
    have hiClose : dist (centers i.val) (pick i).val < R / 2 :=
      (Classical.choose_spec (hNet i.val i.property)).2
    have hjClose := (Classical.choose_spec (hNet j.val j.property)).2
    have hdist : dist (centers i.val) (centers j.val) < R := by
      have ht := dist_triangle (centers i.val) (pick i).val (centers j.val)
      have hj' : dist (pick i).val (centers j.val) < R / 2 := by
        rw [hz, dist_comm]
        exact hjClose
      linarith
    have hd := hDisjoint i.val i.property j.val j.property hij
    have hmem : centers i.val ∈ Metric.ball (centers j.val) R :=
      Metric.mem_ball.mpr hdist
    exact (Set.disjoint_left.mp hd)
      (Metric.mem_ball_self hR) hmem
  have hc := Fintype.card_le_of_injective pick hpick
  simpa only [Fintype.card_coe] using hc

/-- Transverse original tubes meet at most `L` disjoint localization balls,
provided the ambient ball of radius `(4 + 8/θ)R` has a radius-`R/2`
net of at most `L` points. -/
theorem two_transverse_tubes_ball_count_of_cover
    {n : ℕ} {I : Type*}
    (p q u v : Kakeya.Space n) (δ R θ : ℝ) (L : ℕ)
    (hR : 0 < R) (hδR : δ ≤ R) (hθ : 0 < θ)
    (hu : ‖u‖ = 1)
    (hTrans : TransverseDirections u v θ)
    (centers : I → Kakeya.Space n) (J : Finset I)
    (hDisjoint : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (Metric.ball (centers i) R) (Metric.ball (centers j) R))
    (hParent : ∀ i ∈ J,
      (Metric.ball (centers i) R ∩ Kakeya.unitTube p u δ).Nonempty)
    (hOther : ∀ i ∈ J,
      (Metric.ball (centers i) R ∩ Kakeya.unitTube q v δ).Nonempty)
    (hCover : ∀ c : Kakeya.Space n,
      ∃ Z : Finset (Kakeya.Space n), Z.card ≤ L ∧
        ∀ x : Kakeya.Space n,
          dist x c ≤ (4 + 8 / θ) * R →
            ∃ z ∈ Z, dist x z < R / 2) :
    J.card ≤ L := by
  classical
  by_cases hJ : J.Nonempty
  · obtain ⟨i0, hi0⟩ := hJ
    obtain ⟨Z, hZ, hNet⟩ := hCover (centers i0)
    apply (disjoint_balls_card_le_half_radius_net centers R hR
      J Z hDisjoint ?_).trans hZ
    intro i hi
    apply hNet
    exact two_transverse_tubes_ball_center_diameter
      p q u v (centers i) (centers i0) δ R θ hθ hδR hu hTrans
      (hParent i hi) (hOther i hi) (hParent i0 hi0) (hOther i0 hi0)
  · have hempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [hempty]

end Kakeya.Ninety21
