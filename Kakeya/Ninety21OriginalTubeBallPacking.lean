module
public import Kakeya.Ninety21GreedyVitaliBounds
public import Kakeya.Eighty9ArbitraryOrientationTubeBall

/-!
# Original-tube localization-ball geometry

A radius-`R` ball meeting a `δ`-tube, with `δ ≤ R`, is contained in
the `3R`-neighborhood of the tube's central segment. A disjoint finite
family of measurable balls satisfies the corresponding volume-sum bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Kakeya.Ninety21

/-- A radius-`R` ball meeting an original tube lies within distance `3R`
of a point on the central segment of that tube. -/
theorem originalTube_intersecting_ball_subset_axisNeighborhood
    {n : ℕ} (p v b : Kakeya.Space n) (δ R : ℝ)
    (hδR : δ ≤ R)
    (hHit : (Metric.ball b R ∩ Kakeya.unitTube p v δ).Nonempty) :
    Metric.ball b R ⊆
      {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧
        dist y (p + t • v) < 3 * R} := by
  obtain ⟨x, hxb, hxt⟩ := hHit
  obtain ⟨t, w, ht, _hw, hnorm, hx⟩ := hxt
  subst x
  intro y hy
  refine ⟨t, ht, ?_⟩
  have h1 : dist y b < R := Metric.mem_ball.mp hy
  have h2 : dist b (p + t • v + w) < R := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hxb)
  have h3 : dist (p + t • v + w) (p + t • v) ≤ δ := by
    have heq : (p + t • v + w) - (p + t • v) = w := by
      abel
    simpa only [dist_eq_norm, heq] using hnorm
  have htri : dist y (p + t • v) ≤
      dist y b + dist b (p + t • v + w) +
        dist (p + t • v + w) (p + t • v) := by
    have ha := dist_triangle y b (p + t • v + w)
    have hb := dist_triangle y (p + t • v + w) (p + t • v)
    linarith
  linarith

/-- The sum of the volumes of disjoint measurable localized balls does not
exceed the volume of a set containing them all. -/
theorem disjoint_localization_balls_volume_sum_le
    {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (balls : I → Set X) (s : Finset I) (E : Set X)
    (hd : (↑s : Set I).PairwiseDisjoint balls)
    (hm : ∀ i ∈ s, MeasurableSet (balls i))
    (hsub : ∀ i ∈ s, balls i ⊆ E) :
    (∑ i ∈ s, μ (balls i)) ≤ μ E := by
  have hUnion : (⋃ i ∈ s, balls i) ⊆ E := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact hsub i his hxi
  calc
    (∑ i ∈ s, μ (balls i)) = μ (⋃ i ∈ s, balls i) :=
      (measure_biUnion_finset hd hm).symm
    _ ≤ μ E := measure_mono hUnion

/-! ## Orthogonal cylinder bound for the original tube -/

/-- The radius-`a` neighborhood of the central segment of a length-one tube
has volume at most the product of a length-`1 + 2a` interval and a
transverse radius-`a` ball. -/
theorem originalTube_axisNeighborhood_volume_le
    {n : ℕ} (p v : Kakeya.Space n) (a : ℝ)
    (hNorm : ‖v‖ ≤ 1) :
    (volume : Measure (Kakeya.Space n))
      {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧
        dist y (p + t • v) < a} ≤
      (volume : Measure ↥(Kakeya.TubeBall.directionLine v))
        (Metric.closedBall 0 ((1 : ℝ) / 2 + a)) *
      (volume : Measure ↥((Kakeya.TubeBall.directionLine v)ᗮ))
        (Metric.closedBall 0 a) := by
  let s : Submodule ℝ (Kakeya.Space n) := Kakeya.TubeBall.directionLine v
  let c := Kakeya.TubeBall.directionCoordinates p v
  let axial : Set ↥s := Metric.closedBall 0 ((1 : ℝ) / 2 + a)
  let transverse : Set ↥(sᗮ) := Metric.closedBall 0 a
  have hsub :
      {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧ dist y (p + t • v) < a} ⊆
        c ⁻¹' (axial ×ˢ transverse) := by
    intro y hy
    obtain ⟨t, ht, hy⟩ := hy
    let x : Kakeya.Space n := p + t • v
    have hx : y ∈ Metric.closedBall x a :=
      Metric.mem_closedBall.mpr (le_of_lt hy)
    have hline : t • v ∈ s :=
      Submodule.smul_mem s t (Submodule.mem_span_singleton_self v)
    have hshift : x - p = t • v := by
      dsimp [x]
      abel
    have hAxZero : (c x).1 = (⟨t • v, hline⟩ : s) := by
      simp only [c, Kakeya.TubeBall.directionCoordinates,
        Submodule.measurableEquivProd_apply, vsub_eq_sub]
      rw [hshift]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨t • v, hline⟩
    have hPerpZero : (c x).2 = 0 := by
      simp only [c, Kakeya.TubeBall.directionCoordinates,
        Submodule.measurableEquivProd_apply, vsub_eq_sub]
      rw [hshift]
      exact Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hline
    have hAx : dist (c y).1 (c x).1 ≤ a :=
      Metric.mem_closedBall.mp
        (Kakeya.TubeBall.directionCoordinates_axis_ball p v x y a hx)
    have hAxOrigin : dist (c x).1 0 ≤ (1 : ℝ) / 2 := by
      rw [hAxZero, dist_zero_right]
      change ‖t • v‖ ≤ (1 : ℝ) / 2
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |t| * ‖v‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hNorm (abs_nonneg t)
        _ ≤ (1 : ℝ) / 2 := by simpa using ht
    have hAxBound : dist (c y).1 0 ≤ (1 : ℝ) / 2 + a := by
      calc
        dist (c y).1 0 ≤ dist (c y).1 (c x).1 + dist (c x).1 0 :=
          dist_triangle _ _ _
        _ ≤ a + (1 : ℝ) / 2 := add_le_add hAx hAxOrigin
        _ = (1 : ℝ) / 2 + a := by ring
    have hdistShift : dist (y - p) (x - p) = dist y x := by
      simp only [dist_eq_norm]
      congr 1
      abel
    have hPerp : dist (c y).2 (c x).2 ≤ dist y x := by
      have h := ((sᗮ).lipschitzWith_orthogonalProjectionOnto).dist_le_mul
        (y - p) (x - p)
      simp only [c, Kakeya.TubeBall.directionCoordinates,
        Submodule.measurableEquivProd_apply, vsub_eq_sub]
      simpa only [NNReal.coe_one, one_mul, hdistShift] using h
    have hPerpBound : dist (c y).2 0 ≤ a := by
      rw [← hPerpZero]
      exact hPerp.trans (le_of_lt hy)
    change c y ∈ axial ×ˢ transverse
    exact ⟨Metric.mem_closedBall.mpr hAxBound,
      Metric.mem_closedBall.mpr hPerpBound⟩
  calc
    (volume : Measure (Kakeya.Space n))
        {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧ dist y (p + t • v) < a} ≤
      (volume : Measure (Kakeya.Space n)) (c ⁻¹' (axial ×ˢ transverse)) :=
        measure_mono hsub
    _ ≤ (volume : Measure (↥s × ↥(sᗮ))) (axial ×ˢ transverse) :=
      (Kakeya.TubeBall.directionCoordinates_measurePreserving p v).measure_preimage_le _
    _ = (volume : Measure ↥s) axial *
        (volume : Measure ↥(sᗮ)) transverse := by
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    _ = _ := rfl

/-- A disjoint family of radius-`R` balls meeting a unit tube satisfies
the geometric volume comparison in Lemma 4.4. -/
theorem originalTube_disjoint_balls_volume_le
    {n : ℕ} {I : Type*} (p v : Kakeya.Space n)
    (δ R : ℝ) (centers : I → Kakeya.Space n) (s : Finset I)
    (hNorm : ‖v‖ ≤ 1) (hδR : δ ≤ R)
    (hd : (↑s : Set I).PairwiseDisjoint (fun i => Metric.ball (centers i) R))
    (hHit : ∀ i ∈ s,
      (Metric.ball (centers i) R ∩ Kakeya.unitTube p v δ).Nonempty) :
    (s.card : ℝ≥0∞) *
      (volume : Measure (Kakeya.Space n))
        (Metric.ball (0 : Kakeya.Space n) R) ≤
      (volume : Measure ↥(Kakeya.TubeBall.directionLine v))
        (Metric.closedBall 0 ((1 : ℝ) / 2 + 3 * R)) *
      (volume : Measure ↥((Kakeya.TubeBall.directionLine v)ᗮ))
        (Metric.closedBall 0 (3 * R)) := by
  let E : Set (Kakeya.Space n) :=
    {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧ dist y (p + t • v) < 3 * R}
  have hSub (i : I) (hi : i ∈ s) : Metric.ball (centers i) R ⊆ E :=
    originalTube_intersecting_ball_subset_axisNeighborhood
      p v (centers i) δ R hδR (hHit i hi)
  have hVolumes :
      (∑ i ∈ s, (volume : Measure (Kakeya.Space n))
        (Metric.ball (centers i) R)) =
      (s.card : ℝ≥0∞) *
        (volume : Measure (Kakeya.Space n))
          (Metric.ball (0 : Kakeya.Space n) R) := by
    have hEqual (i : I) :
        (volume : Measure (Kakeya.Space n)) (Metric.ball (centers i) R) =
        (volume : Measure (Kakeya.Space n))
          (Metric.ball (0 : Kakeya.Space n) R) := by
      exact Measure.addHaar_ball_center volume (centers i) R
    calc
      (∑ i ∈ s, (volume : Measure (Kakeya.Space n))
          (Metric.ball (centers i) R)) =
        ∑ _i ∈ s, (volume : Measure (Kakeya.Space n))
          (Metric.ball (0 : Kakeya.Space n) R) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hEqual i
      _ = (s.card : ℝ≥0∞) *
          (volume : Measure (Kakeya.Space n))
            (Metric.ball (0 : Kakeya.Space n) R) := by simp [nsmul_eq_mul]
  calc
    (s.card : ℝ≥0∞) *
        (volume : Measure (Kakeya.Space n))
          (Metric.ball (0 : Kakeya.Space n) R) =
      ∑ i ∈ s, (volume : Measure (Kakeya.Space n))
        (Metric.ball (centers i) R) := hVolumes.symm
    _ ≤ (volume : Measure (Kakeya.Space n)) E :=
      disjoint_localization_balls_volume_sum_le
        (volume : Measure (Kakeya.Space n))
        (fun i => Metric.ball (centers i) R) s E hd
        (fun i hi => Metric.isOpen_ball.measurableSet) hSub
    _ ≤ _ := originalTube_axisNeighborhood_volume_le p v (3 * R)
      hNorm

/-- Cancelling the common transverse power in Lemma 4.4's volume bound. -/
theorem disjoint_balls_card_le_from_volume
    (k M : ℕ) (R ωn ωtrans : ℝ) (hR : 0 < R) (hRone : R ≤ 1)
    (hωn : 0 < ωn) (hωtrans : 0 ≤ ωtrans)
    (hVolume : (M : ℝ) * (R ^ (k + 2) * ωn) ≤
      (1 + 6 * R) * ((3 * R) ^ (k + 1) * ωtrans)) :
    (M : ℝ) ≤ (7 * 3 ^ (k + 1) * ωtrans) / (ωn * R) := by
  have hpow : 0 < R ^ (k + 1) := pow_pos hR _
  have hfactor :
      ((M : ℝ) * ωn * R) * R ^ (k + 1) ≤
        (7 * 3 ^ (k + 1) * ωtrans) * R ^ (k + 1) := by
    calc
      ((M : ℝ) * ωn * R) * R ^ (k + 1) =
        (M : ℝ) * (R ^ (k + 2) * ωn) := by
          rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
          ring
      _ ≤ (1 + 6 * R) * ((3 * R) ^ (k + 1) * ωtrans) := hVolume
      _ = ((1 + 6 * R) * 3 ^ (k + 1) * ωtrans) * R ^ (k + 1) := by
          rw [mul_pow]
          ring
      _ ≤ (7 * 3 ^ (k + 1) * ωtrans) * R ^ (k + 1) := by
          have hscale : 1 + 6 * R ≤ 7 := by linarith
          have hnonneg : 0 ≤ 3 ^ (k + 1) * ωtrans * R ^ (k + 1) := by
            positivity
          nlinarith [mul_le_mul_of_nonneg_right hscale hnonneg]
  have hbasic := (mul_le_mul_iff_left₀ hpow).mp hfactor
  exact (le_div_iff₀ (mul_pos hωn hR)).mpr (by nlinarith [hbasic])

/-- Numerical dyadic scaling of the volume-packing inequality. -/
theorem disjoint_balls_card_le_dyadic
    (k M : ℕ) (R A q ωn ωtrans : ℝ)
    (hR : 0 < R) (hRone : R ≤ 1)
    (hA : 0 < A) (hq : 0 < q)
    (hωn : 0 < ωn) (hωtrans : 0 ≤ ωtrans)
    (hScale : q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) * R = A)
    (hVolume : (M : ℝ) * (R ^ (k + 2) * ωn) ≤
      (1 + 6 * R) * ((3 * R) ^ (k + 1) * ωtrans)) :
    (M : ℝ) ≤
      ((7 * 3 ^ (k + 1) * ωtrans) / (ωn * A)) *
        q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
  let e : ℝ := (1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)
  have hPow : 0 ≤ q ^ e := le_of_lt (Real.rpow_pos_of_pos hq e)
  have hbase : (M : ℝ) * ωn * R ≤ 7 * 3 ^ (k + 1) * ωtrans := by
    have h := disjoint_balls_card_le_from_volume k M R ωn ωtrans
      hR hRone hωn hωtrans hVolume
    have hmul := (le_div_iff₀ (mul_pos hωn hR)).mp h
    nlinarith [hmul]
  have hscaled : (M : ℝ) * (ωn * A) ≤
      (7 * 3 ^ (k + 1) * ωtrans) * q ^ e := by
    calc
      (M : ℝ) * (ωn * A) = ((M : ℝ) * ωn * R) * q ^ e := by
        rw [← hScale]
        ring
      _ ≤ (7 * 3 ^ (k + 1) * ωtrans) * q ^ e :=
        mul_le_mul_of_nonneg_right hbase hPow
  have hdiv := (le_div_iff₀ (mul_pos hωn hA)).mpr hscaled
  calc
    (M : ℝ) ≤ (7 * 3 ^ (k + 1) * ωtrans) * q ^ e / (ωn * A) := hdiv
    _ = ((7 * 3 ^ (k + 1) * ωtrans) / (ωn * A)) *
          q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
          dsimp [e]
          ring

/-- Volume of the radius-one ball in `d`-dimensional Euclidean space. -/
noncomputable def packingBallConstant (d : ℕ) : ℝ :=
  √Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The volume coefficient is strictly positive in every dimension. -/
theorem packingBallConstant_pos (d : ℕ) : 0 < packingBallConstant d := by
  unfold packingBallConstant
  have hGamma : 0 < Real.Gamma ((d : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  exact div_pos (pow_pos (Real.sqrt_pos.2 Real.pi_pos) _) hGamma

/-- The explicit real-volume inequality furnished by Euclidean packing. -/
theorem originalTube_disjoint_balls_real_volume_le
    (k : ℕ) {I : Type*} (p v : Kakeya.Space (k + 2))
    (δ R : ℝ) (centers : I → Kakeya.Space (k + 2)) (s : Finset I)
    (hv : v ≠ 0) (hNorm : ‖v‖ ≤ 1) (hR : 0 < R) (hδR : δ ≤ R)
    (hd : (↑s : Set I).PairwiseDisjoint (fun i => Metric.ball (centers i) R))
    (hHit : ∀ i ∈ s,
      (Metric.ball (centers i) R ∩ Kakeya.unitTube p v δ).Nonempty) :
    (s.card : ℝ) * (R ^ (k + 2) * packingBallConstant (k + 2)) ≤
      (1 + 6 * R) * ((3 * R) ^ (k + 1) * packingBallConstant (k + 1)) := by
  have hmeasure := originalTube_disjoint_balls_volume_le p v δ R centers s
    hNorm hδR hd hHit
  have hvolume_ball :
      (volume : Measure (Kakeya.Space (k + 2)))
          (Metric.ball (0 : Kakeya.Space (k + 2)) R) =
        ENNReal.ofReal R ^ (k + 2) *
          ENNReal.ofReal (packingBallConstant (k + 2)) := by
    simpa only [Kakeya.Space, packingBallConstant, Fintype.card_fin] using
      (EuclideanSpace.volume_ball (Fin (k + 2))
        (0 : Kakeya.Space (k + 2)) R)
  have hvolume_axis :
      (volume : Measure ↥(Kakeya.TubeBall.directionLine v))
          (Metric.closedBall 0 ((1 : ℝ) / 2 + 3 * R)) =
        ENNReal.ofReal (1 + 6 * R) := by
    have h := Kakeya.TubeBall.directionLine_closedBall_volume
      (0 : Kakeya.Space (k + 2)) v (0 : Kakeya.Space (k + 2))
      ((1 : ℝ) / 2 + 3 * R) hv (by positivity)
    convert h using 1
    · simp [Kakeya.TubeBall.directionCoordinates,
        Submodule.measurableEquivProd_apply]
    · congr 1
      ring
  have hvolume_transverse :
      (volume : Measure ↥((Kakeya.TubeBall.directionLine v)ᗮ))
          (Metric.closedBall 0 (3 * R)) =
        ENNReal.ofReal (3 * R) ^ (k + 1) *
          ENNReal.ofReal (packingBallConstant (k + 1)) := by
    simpa only [packingBallConstant] using
      (Kakeya.TubeBall.transverse_closedBall_volume v (3 * R) hv)
  rw [hvolume_ball, hvolume_axis, hvolume_transverse] at hmeasure
  have hfinite :
      ENNReal.ofReal (1 + 6 * R) *
        (ENNReal.ofReal (3 * R) ^ (k + 1) *
          ENNReal.ofReal (packingBallConstant (k + 1))) ≠ ⊤ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  have hR0 : 0 ≤ R := hR.le
  have h6R : 0 ≤ 1 + 6 * R := by positivity
  have h3R : 0 ≤ 3 * R := by positivity
  have hωn : 0 ≤ packingBallConstant (k + 2) :=
    (packingBallConstant_pos _).le
  have hωtrans : 0 ≤ packingBallConstant (k + 1) :=
    (packingBallConstant_pos _).le
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR0, ENNReal.toReal_ofReal h6R,
    ENNReal.toReal_ofReal h3R,
    ENNReal.toReal_ofReal hωn, ENNReal.toReal_ofReal hωtrans,
    ENNReal.toReal_natCast] using hreal

/-- Lemma 4.4: a tube of length at most one meets at most `O(1/R)`
mutually disjoint balls of radius `R`, with an explicit coefficient. -/
theorem originalTube_disjoint_balls_card_le
    (k : ℕ) {I : Type*} (p v : Kakeya.Space (k + 2))
    (δ R : ℝ) (centers : I → Kakeya.Space (k + 2)) (s : Finset I)
    (hv : v ≠ 0) (hNorm : ‖v‖ ≤ 1)
    (hR : 0 < R) (hRone : R ≤ 1) (hδR : δ ≤ R)
    (hd : (↑s : Set I).PairwiseDisjoint (fun i => Metric.ball (centers i) R))
    (hHit : ∀ i ∈ s,
      (Metric.ball (centers i) R ∩ Kakeya.unitTube p v δ).Nonempty) :
    (s.card : ℝ) ≤
      (7 * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
        (packingBallConstant (k + 2) * R) := by
  exact disjoint_balls_card_le_from_volume k s.card R
    (packingBallConstant (k + 2)) (packingBallConstant (k + 1))
    hR hRone (packingBallConstant_pos _) (packingBallConstant_pos _).le
    (originalTube_disjoint_balls_real_volume_le k p v δ R centers s
      hv hNorm hR hδR hd hHit)

end Kakeya.Ninety21
