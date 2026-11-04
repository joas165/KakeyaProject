module
public import Kakeya.Geometry

/-!
# Tube-ball volume bound: longitudinal times transverse measure

This file proves the tube-ball bound in a straightened coordinate model:
`ℝ × EuclideanSpace ℝ (Fin (k+1))`, with Lebesgue product measure.

The axis is the first real coordinate.  The transverse cross-section is
an `(k+1)`-dimensional Euclidean ball, so total dimension is `k+2`.
The bound is `2*R` times the transverse ball volume; the latter is
`ω_(k+1) * δ^(k+1)`.  It holds for every ball center, with no assumption
that the ball center lies on the tube axis.

The final theorem transfers the result to any measurable space through
an explicitly supplied measure-preserving coordinate map and the two
geometric containment properties.  For an arbitrary `Cordoba.Tube` in
`EuclideanSpace ℝ (Fin n)`, producing that coordinate map and verifying
the containments is a SEPARATE orientation/geometry bridge; this file
does not falsely assert that bridge.

No `sorry`, `admit`, or additional axioms are used in this file.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.TubeBall

/-- The `(k+1)`-dimensional transverse Euclidean space. -/
abbrev Transverse (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1))

/-- Straightened tube coordinates: one longitudinal and `k+1`
transverse coordinates. -/
abbrev Axial (k : ℕ) := ℝ × Transverse k

/-- The infinite straight cylinder of transverse radius `δ` and
transverse center `p`.  A finite unit tube is a subset of this set. -/
def straightTube (k : ℕ) (p : Transverse k) (δ : ℝ) : Set (Axial k) :=
  {z | z.2 ∈ Metric.closedBall p δ}

/-- The tube/ball intersection lies in a longitudinal segment of radius
`R` times the entire transverse disk of radius `δ`.
The product metric is the maximum of the component distances, so this
containment is immediate from `Prod.dist_eq`. -/
theorem straightTube_inter_ball_subset_product
    (k : ℕ) (p : Transverse k) (c : Axial k) (δ R : ℝ) :
    straightTube k p δ ∩ Metric.closedBall c R ⊆
      Metric.closedBall c.1 R ×ˢ Metric.closedBall p δ := by
  intro z hz
  change z ∈ straightTube k p δ ∧ z ∈ Metric.closedBall c R at hz
  have hzTube : z.2 ∈ Metric.closedBall p δ := hz.1
  have hzBall : dist z c ≤ R := Metric.mem_closedBall.mp hz.2
  have hzFirst : dist z.1 c.1 ≤ R := by
    rw [Prod.dist_eq] at hzBall
    exact (le_max_left _ _).trans hzBall
  change z.1 ∈ Metric.closedBall c.1 R ∧
    z.2 ∈ Metric.closedBall p δ
  exact ⟨Metric.mem_closedBall.mpr hzFirst, hzTube⟩

/-- **The tube-ball volume bound**, in straightened coordinates.

The estimate is valid for all real `δ` and `R`; negative radii just
make the relevant closed balls empty.  In dimension `n = k+2`, the
right-hand transverse factor is `ω_(n-1) δ^(n-1)` for nonnegative δ.
The measure is the actual Lebesgue product measure, not a counting
measure and not a newly assumed tube-ball inequality. -/
theorem straightTube_inter_ball_volume_le
    (k : ℕ) (p : Transverse k) (c : Axial k) (δ R : ℝ) :
    (volume : Measure (Axial k))
        (straightTube k p δ ∩ Metric.closedBall c R) ≤
      ENNReal.ofReal (2 * R) *
        (volume : Measure (Transverse k)) (Metric.closedBall p δ) := by
  calc
    (volume : Measure (Axial k))
        (straightTube k p δ ∩ Metric.closedBall c R) ≤
        (volume : Measure (Axial k))
          (Metric.closedBall c.1 R ×ˢ Metric.closedBall p δ) :=
      measure_mono (straightTube_inter_ball_subset_product k p c δ R)
    _ = (volume : Measure ℝ) (Metric.closedBall c.1 R) *
          (volume : Measure (Transverse k)) (Metric.closedBall p δ) := by
      simp only [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    _ = ENNReal.ofReal (2 * R) *
          (volume : Measure (Transverse k)) (Metric.closedBall p δ) := by
      rw [Real.volume_closedBall]

/-- The explicit `2 ω_(n-1) R δ^(n-1)` form, with `n = k+2`.
It uses Mathlib's exact Euclidean-ball volume formula. -/
theorem straightTube_inter_ball_volume_le_explicit
    (k : ℕ) (p : Transverse k) (c : Axial k) (δ R : ℝ) :
    (volume : Measure (Axial k))
        (straightTube k p δ ∩ Metric.closedBall c R) ≤
      ENNReal.ofReal (2 * R) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
  simpa only [EuclideanSpace.volume_closedBall, Fintype.card_fin]
    using straightTube_inter_ball_volume_le k p c δ R

/-- Any shorter axial tube or extra restriction of the tube has the
same upper bound. -/
theorem subsetTube_inter_ball_volume_le
    (k : ℕ) (p : Transverse k) (c : Axial k)
    (T : Set (Axial k)) (δ R : ℝ)
    (hT : T ⊆ straightTube k p δ) :
    (volume : Measure (Axial k)) (T ∩ Metric.closedBall c R) ≤
      ENNReal.ofReal (2 * R) *
        (volume : Measure (Transverse k)) (Metric.closedBall p δ) := by
  have hsub : T ∩ Metric.closedBall c R ⊆
      straightTube k p δ ∩ Metric.closedBall c R := by
    intro z hz
    exact ⟨hT hz.1, hz.2⟩
  exact (measure_mono hsub).trans
    (straightTube_inter_ball_volume_le k p c δ R)

/-- Transport the tube-ball inequality to any ambient measure space,
provided we have straightened coordinates preserving volume.

`hTube` and `hBall` are **geometric containment checks**, NOT an assumed
volume inequality.  For a rotated/translated Euclidean line tube they
must be established by constructing an orthonormal coordinate frame.
The map need not be injective for this inequality: measure preservation
and preimage monotonicity are enough. -/
theorem tubeBall_volume_le_of_measurePreserving_coordinates
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (k : ℕ) (coords : X → Axial k)
    (hcoords : MeasurePreserving coords μ volume)
    (T B : Set X) (p : Transverse k) (c : Axial k) (δ R : ℝ)
    (hTube : T ⊆ coords ⁻¹' straightTube k p δ)
    (hBall : B ⊆ coords ⁻¹' Metric.closedBall c R) :
    μ (T ∩ B) ≤
      ENNReal.ofReal (2 * R) *
        (volume : Measure (Transverse k)) (Metric.closedBall p δ) := by
  have hsubset : T ∩ B ⊆
      coords ⁻¹' (straightTube k p δ ∩ Metric.closedBall c R) := by
    intro x hx
    exact ⟨hTube hx.1, hBall hx.2⟩
  calc
    μ (T ∩ B) ≤ μ
        (coords ⁻¹' (straightTube k p δ ∩ Metric.closedBall c R)) :=
      measure_mono hsubset
    _ ≤ (volume : Measure (Axial k))
        (straightTube k p δ ∩ Metric.closedBall c R) :=
      hcoords.measure_preimage_le _
    _ ≤ ENNReal.ofReal (2 * R) *
        (volume : Measure (Transverse k)) (Metric.closedBall p δ) :=
      straightTube_inter_ball_volume_le k p c δ R

/-- Specialize the transfer theorem to the project's actual finite-length
`Kakeya.unitTube`.  The two coordinate-containment hypotheses are the
orientation bridge that remains to be established for arbitrary `p` and
unit direction `v`.  The measure estimate itself is a conclusion. -/
theorem unitTube_ball_volume_le_of_frame
    (k : ℕ) (p v b : Kakeya.Space (k + 2)) (δ R : ℝ)
    (coords : Kakeya.Space (k + 2) → Axial k)
    (hcoords : MeasurePreserving coords
      (volume : Measure (Kakeya.Space (k + 2))) volume)
    (transverseCenter : Transverse k) (c : Axial k)
    (hTube : Kakeya.unitTube p v δ ⊆
      coords ⁻¹' straightTube k transverseCenter δ)
    (hBall : Metric.closedBall b R ⊆
      coords ⁻¹' Metric.closedBall c R) :
    (volume : Measure (Kakeya.Space (k + 2)))
      (Kakeya.unitTube p v δ ∩ Metric.closedBall b R) ≤
      ENNReal.ofReal (2 * R) *
        (volume : Measure (Transverse k))
          (Metric.closedBall transverseCenter δ) := by
  exact tubeBall_volume_le_of_measurePreserving_coordinates
    (volume : Measure (Kakeya.Space (k + 2))) k coords hcoords
    (Kakeya.unitTube p v δ) (Metric.closedBall b R)
    transverseCenter c δ R hTube hBall

end Kakeya.TubeBall
