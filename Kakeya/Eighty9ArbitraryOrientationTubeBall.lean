module
public import Kakeya.Eighty5TubeBallVolume
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Arbitrary-direction orthogonal coordinates for the tube-ball estimate

The earlier straight-coordinate proof treated the axial product `ℝ × E` and
assumed a measure-preserving chart to transport its estimate.  Here the chart
is constructed *canonically* for every direction `v`: Mathlib's orthogonal
measurable equivalence with respect to the line `ℝ ∙ v`.

This removes the **measure-preserving-coordinate hypothesis** rather than
postulating a new coordinate system or an additional axiom.  The resulting
product bound is orientation-independent.  Converting its one-dimensional
axis factor and `(n-1)`-dimensional transverse factor into
`2 * R * ω_(n-1) * δ^(n-1)` is a separate scalar simplification.

The principal statements do not use `LowerIncidence` or directional packing.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.TubeBall

/-- The line in the direction `v` (also meaningful when `v = 0`). -/
abbrev directionLine {n : ℕ} (v : Kakeya.Space n) :
    Submodule ℝ (Kakeya.Space n) := ℝ ∙ v

/-- Canonical longitudinal/transverse coordinates centered at `p`.
No orientation, frame, or coordinate hypothesis is supplied. -/
noncomputable def directionCoordinates {n : ℕ}
    (p v : Kakeya.Space n) :
    Kakeya.Space n ≃ᵐ
      (↥(directionLine v) × ↥((directionLine v)ᗮ)) :=
  (directionLine v).measurableEquivProd p

/-- The canonical orthogonal-coordinate chart preserves the actual Euclidean
volume for every direction, without a postulated rotation/frame. -/
theorem directionCoordinates_measurePreserving {n : ℕ}
    (p v : Kakeya.Space n) :
    MeasurePreserving (directionCoordinates p v)
      (volume : Measure (Kakeya.Space n))
      (volume : Measure (↥(directionLine v) × ↥((directionLine v)ᗮ))) := by
  simpa only [directionCoordinates,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    (directionLine v).measurePreserving_measurableEquivProd p

/-- Read the transverse coordinate directly from Mathlib's product chart.
Keeping this as a separate lemma avoids unfolding the measurable equivalence
inside the geometric projection argument. -/
private theorem directionCoordinates_snd {n : ℕ}
    (p v x : Kakeya.Space n) :
    (directionCoordinates p v x).2 =
      ((directionLine v)ᗮ).orthogonalProjectionOnto (x - p) := by
  simp only [directionCoordinates, Submodule.measurableEquivProd_apply,
    vsub_eq_sub]

set_option maxHeartbeats 800000 in
/-- The transverse coordinate of the finite line tube is in the disk of
radius `δ`.  The direction is arbitrary, and no unit-vector assumption is
needed for this geometric containment. -/
theorem unitTube_transverse_coordinate_bound {n : ℕ}
    (p v : Kakeya.Space n) (δ : ℝ) :
    Kakeya.unitTube p v δ ⊆
      {x | (directionCoordinates p v x).2 ∈
        Metric.closedBall (0 : ↥((directionLine v)ᗮ)) δ} := by
  intro x hx
  obtain ⟨t, w, _ht, hw, hnorm, rfl⟩ := hx
  let s : Submodule ℝ (Kakeya.Space n) := directionLine v
  have hwperp : w ∈ sᗮ :=
    (Submodule.mem_orthogonal_singleton_iff_inner_left).2 hw
  have hvline : t • v ∈ s :=
    Submodule.smul_mem s t (Submodule.mem_span_singleton_self v)
  have hvzero : (sᗮ).orthogonalProjectionOnto (t • v) = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hvline
  have hwself : (sᗮ).orthogonalProjectionOnto w =
      (⟨w, hwperp⟩ : sᗮ) :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨w, hwperp⟩
  have hshift : (p + t • v + w) - p = t • v + w := by
    abel
  have hproj : (sᗮ).orthogonalProjectionOnto
      ((p + t • v + w) - p) = (⟨w, hwperp⟩ : sᗮ) := by
    rw [hshift, map_add, hvzero, hwself, zero_add]
  have hnorm' : ‖(⟨w, hwperp⟩ : sᗮ)‖ ≤ δ := by
    -- Submodule elements carry the norm of their underlying vector.
    change ‖w‖ ≤ δ
    exact hnorm
  -- A set-comprehension membership is not yet an exposed coordinate equation.
  -- Reduce it once, then rewrite the projection by the already proved identity.
  change (directionCoordinates p v (p + t • v + w)).2 ∈
    Metric.closedBall (0 : sᗮ) δ
  rw [directionCoordinates_snd p v (p + t • v + w), hproj]
  apply Metric.mem_closedBall.mpr
  rw [dist_eq_norm, sub_zero]
  exact hnorm'

/-- Each axial coordinate is 1-Lipschitz, so a ball of radius `R`
projects into a ball of the *same* radius in the axial subspace. -/
theorem directionCoordinates_axis_ball {n : ℕ}
    (p v b x : Kakeya.Space n) (R : ℝ)
    (hx : x ∈ Metric.closedBall b R) :
    (directionCoordinates p v x).1 ∈
      Metric.closedBall (directionCoordinates p v b).1 R := by
  have hdist :=
    ((directionLine v).lipschitzWith_orthogonalProjectionOnto).dist_le_mul
      (x - p) (b - p)
  have hshift : dist (x - p) (b - p) = dist x b := by
    simp only [dist_eq_norm]
    congr 1
    abel
  have hproj :
      dist ((directionLine v).orthogonalProjectionOnto (x - p))
        ((directionLine v).orthogonalProjectionOnto (b - p)) ≤ R := by
    calc
      _ ≤ dist (x - p) (b - p) := by simpa using hdist
      _ = dist x b := hshift
      _ ≤ R := Metric.mem_closedBall.mp hx
  simpa only [Metric.mem_closedBall, directionCoordinates,
    Submodule.measurableEquivProd_apply, vsub_eq_sub, Prod.fst] using hproj

/-- **Orientation-independent product estimate for the actual unit tube**.
The coordinate equivalence is constructed and proved volume preserving above;
no chart or geometric containment hypotheses appear in this theorem.

The two factors are actual Haar volumes of balls in the axial line and its
orthogonal complement.  The standard explicit `2 R ω_(n-1) δ^(n-1)`
form is obtained by calculating these dimensions and their ball volumes. -/
theorem unitTube_ball_volume_le_orthogonal_product {n : ℕ}
    (p v b : Kakeya.Space n) (δ R : ℝ) :
    (volume : Measure (Kakeya.Space n))
        (Kakeya.unitTube p v δ ∩ Metric.closedBall b R) ≤
      (volume : Measure ↥(directionLine v))
        (Metric.closedBall (directionCoordinates p v b).1 R) *
      (volume : Measure ↥((directionLine v)ᗮ))
        (Metric.closedBall 0 δ) := by
  let c := directionCoordinates p v
  let axial : Set ↥(directionLine v) :=
    Metric.closedBall (c b).1 R
  let transverse : Set ↥((directionLine v)ᗮ) :=
    Metric.closedBall 0 δ
  have hsubset : Kakeya.unitTube p v δ ∩ Metric.closedBall b R ⊆
      c ⁻¹' (axial ×ˢ transverse) := by
    intro x hx
    change c x ∈ axial ×ˢ transverse
    exact ⟨directionCoordinates_axis_ball p v b x R hx.2,
      unitTube_transverse_coordinate_bound p v δ hx.1⟩
  calc
    (volume : Measure (Kakeya.Space n))
        (Kakeya.unitTube p v δ ∩ Metric.closedBall b R) ≤
        (volume : Measure (Kakeya.Space n))
          (c ⁻¹' (axial ×ˢ transverse)) := measure_mono hsubset
    _ ≤ (volume : Measure (↥(directionLine v) × ↥((directionLine v)ᗮ)))
          (axial ×ˢ transverse) :=
      (directionCoordinates_measurePreserving p v).measure_preimage_le _
    _ = (volume : Measure ↥(directionLine v)) axial *
        (volume : Measure ↥((directionLine v)ᗮ)) transverse := by
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    _ = _ := rfl

/-- Gain trimming and restriction to a dyadic set do not increase the
orientation-independent volume bound. -/
theorem localized_unitTube_ball_volume_le_orthogonal_product {n : ℕ}
    (p v b : Kakeya.Space n) (δ R : ℝ) (gain F : Set (Kakeya.Space n)) :
    (volume : Measure (Kakeya.Space n))
      ((((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩ Metric.ball b R)) ≤
      (volume : Measure ↥(directionLine v))
        (Metric.closedBall (directionCoordinates p v b).1 R) *
      (volume : Measure ↥((directionLine v)ᗮ))
        (Metric.closedBall 0 δ) := by
  have hsub :
      (((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩ Metric.ball b R) ⊆
        Kakeya.unitTube p v δ ∩ Metric.closedBall b R := by
    intro x hx
    exact ⟨hx.1.1.1, Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hx.2))⟩
  exact (measure_mono hsub).trans
    (unitTube_ball_volume_le_orthogonal_product p v b δ R)


/-- The axial subspace is genuinely one-dimensional for every nonzero
oriented direction. -/
theorem directionLine_finrank_one {n : ℕ}
    {v : Kakeya.Space n} (hv : v ≠ 0) :
    Module.finrank ℝ ↥(directionLine v) = 1 :=
  finrank_span_singleton hv

/-- In ambient dimension `k+2`, the transverse subspace has dimension `k+1`.
Thus the constant in the product bound is precisely the usual
`(n-1)`-dimensional ball-volume constant. -/
theorem transverse_finrank {k : ℕ}
    {v : Kakeya.Space (k + 2)} (hv : v ≠ 0) :
    Module.finrank ℝ ↥((directionLine v)ᗮ) = k + 1 := by
  have hs := (directionLine v).finrank_add_finrank_orthogonal
  have hdim : Module.finrank ℝ (Kakeya.Space (k + 2)) = k + 2 := by
    simp [Kakeya.Space]
  rw [directionLine_finrank_one hv, hdim] at hs
  omega


/-- The volume of a one-dimensional axial ball is its interval length.
This is independent of which nonzero vector spans the axis. -/
theorem directionLine_closedBall_volume {n : ℕ}
    (p v b : Kakeya.Space n) (R : ℝ)
    (hv : v ≠ 0) (hR : 0 ≤ R) :
    (volume : Measure ↥(directionLine v))
      (Metric.closedBall (directionCoordinates p v b).1 R) =
      ENNReal.ofReal (2 * R) := by
  letI : Nontrivial ↥(directionLine v) :=
    Submodule.nontrivial_span_singleton hv
  have hdim : Module.finrank ℝ ↥(directionLine v) = 1 :=
    directionLine_finrank_one hv
  have hodd : Module.finrank ℝ ↥(directionLine v) = 2 * 0 + 1 := by
    simpa using hdim
  have hvol :
      (volume : Measure ↥(directionLine v))
        (Metric.closedBall (directionCoordinates p v b).1 R) =
        ENNReal.ofReal R * ENNReal.ofReal (2 : ℝ) := by
    rw [InnerProductSpace.volume_closedBall_of_dim_odd hodd]
    simp [hdim, Nat.doubleFactorial]
  calc
    _ = ENNReal.ofReal R * ENNReal.ofReal (2 : ℝ) := hvol
    _ = ENNReal.ofReal (R * 2) := (ENNReal.ofReal_mul hR).symm
    _ = ENNReal.ofReal (2 * R) := by rw [mul_comm]

/-- The transverse `(k+1)`-dimensional disk has the standard Euclidean
ball volume, independently of the orientation of its orthogonal hyperplane. -/
theorem transverse_closedBall_volume {k : ℕ}
    (v : Kakeya.Space (k + 2)) (δ : ℝ) (hv : v ≠ 0) :
    (volume : Measure ↥((directionLine v)ᗮ)) (Metric.closedBall 0 δ) =
      ENNReal.ofReal δ ^ (k + 1) *
        ENNReal.ofReal
          (√Real.pi ^ (k + 1) /
            Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)) := by
  have hdim : Module.finrank ℝ ↥((directionLine v)ᗮ) = k + 1 :=
    transverse_finrank hv
  have hpos : 0 < Module.finrank ℝ ↥((directionLine v)ᗮ) := by
    rw [hdim]
    exact Nat.succ_pos k
  letI : Nontrivial ↥((directionLine v)ᗮ) :=
    Module.nontrivial_of_finrank_pos hpos
  rw [InnerProductSpace.volume_closedBall, hdim]

/-- **Arbitrarily oriented finite unit tube intersected with a ball.**
There is no chart, frame, tube-containment, or volume-bound hypothesis.
Only the geometrically natural nonzero-direction and radius assumptions
remain.  The direction vector does not have to point along a coordinate axis.

Ambient dimension is `n=k+2`, so `n-1=k+1` is the transverse dimension. -/
theorem unitTube_ball_volume_le_explicit_arbitrary_direction
    (k : ℕ) (p v b : Kakeya.Space (k + 2)) (δ R : ℝ)
    (hv : v ≠ 0) (hR : 0 ≤ R) :
    (volume : Measure (Kakeya.Space (k + 2)))
      (Kakeya.unitTube p v δ ∩ Metric.closedBall b R) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
  have hbound := unitTube_ball_volume_le_orthogonal_product p v b δ R
  rw [directionLine_closedBall_volume p v b R hv hR,
    transverse_closedBall_volume v δ hv] at hbound
  exact hbound

/-- The trimmed and dyadic-localized piece of an arbitrary-direction tube
obeys exactly the same explicit volume estimate. -/
theorem localized_unitTube_ball_volume_le_explicit_arbitrary_direction
    (k : ℕ) (p v b : Kakeya.Space (k + 2)) (δ R : ℝ)
    (gain F : Set (Kakeya.Space (k + 2)))
    (hv : v ≠ 0) (hR : 0 ≤ R) :
    (volume : Measure (Kakeya.Space (k + 2)))
      ((((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩ Metric.ball b R)) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
  have hsub :
      (((Kakeya.unitTube p v δ ∩ gain) ∩ F) ∩ Metric.ball b R) ⊆
        Kakeya.unitTube p v δ ∩ Metric.closedBall b R := by
    intro x hx
    exact ⟨hx.1.1.1, Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hx.2))⟩
  exact (measure_mono hsub).trans
    (unitTube_ball_volume_le_explicit_arbitrary_direction k p v b δ R hv hR)

end Kakeya.TubeBall
