module

public import Kakeya.Ninety21AngularChartGeometry

/-!
# Gram identities for separated unit directions

The squared sine of the angle between two unit vectors determines the
transversality inequality. In the two-cap chart it is the squared norm
of the perpendicular coordinate.
-/

@[expose] public section

namespace Kakeya.Ninety21

open scoped InnerProductSpace

/-- Expansion of the two-direction Gram form for unit vectors. -/
theorem unit_directions_gram_identity
    {n : ℕ} (u v : Kakeya.Space n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (a b : ℝ) :
    ‖a • u - b • v‖ ^ 2 =
      (b - a * ⟪u, v⟫_ℝ) ^ 2 +
        a ^ 2 * (1 - ⟪u, v⟫_ℝ ^ 2) := by
  have hnu : ‖a • u‖ ^ 2 = a ^ 2 := by
    rw [norm_smul, hu]
    simp [Real.norm_eq_abs, sq_abs]
  have hnv : ‖b • v‖ ^ 2 = b ^ 2 := by
    rw [norm_smul, hv]
    simp [Real.norm_eq_abs, sq_abs]
  have hin : ⟪a • u, b • v⟫_ℝ = a * b * ⟪u, v⟫_ℝ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hnorm := norm_sub_sq_real (a • u) (b • v)
  rw [hnu, hnv, hin] at hnorm
  calc
    ‖a • u - b • v‖ ^ 2 =
        a ^ 2 - 2 * (a * b * ⟪u, v⟫_ℝ) + b ^ 2 := hnorm
    _ = (b - a * ⟪u, v⟫_ℝ) ^ 2 +
          a ^ 2 * (1 - ⟪u, v⟫_ℝ ^ 2) := by ring

/-- A lower bound on the squared sine yields quantitative transversality. -/
theorem transverse_of_unit_sine_sq_lower
    {n : ℕ} (u v : Kakeya.Space n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hSin : θ ^ 2 ≤ 1 - ⟪u, v⟫_ℝ ^ 2) :
    TransverseDirections u v θ := by
  intro a b
  have hgram := unit_directions_gram_identity u v hu hv a b
  have hmul : a ^ 2 * θ ^ 2 ≤
      a ^ 2 * (1 - ⟪u, v⟫_ℝ ^ 2) :=
    mul_le_mul_of_nonneg_left hSin (sq_nonneg a)
  have hsq : (θ * |a|) ^ 2 ≤ ‖a • u - b • v‖ ^ 2 := by
    rw [hgram]
    nlinarith [sq_nonneg (b - a * ⟪u, v⟫_ℝ), sq_abs a]
  have hleft : 0 ≤ θ * |a| := mul_nonneg hθ (abs_nonneg _)
  have hright : 0 ≤ ‖a • u - b • v‖ := norm_nonneg _
  nlinarith

/-- Failure of quantitative transversality forces a small perpendicular
component in the two-dimensional Gram decomposition. -/
theorem unit_sine_sq_lt_of_not_transverse
    {n : ℕ} (u v : Kakeya.Space n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hNot : ¬ TransverseDirections u v θ) :
    1 - ⟪u, v⟫_ℝ ^ 2 < θ ^ 2 := by
  by_contra h
  exact hNot (transverse_of_unit_sine_sq_lower
    u v hu hv θ hθ (le_of_not_gt h))

/-- The Pythagorean identity converts nontransversality into the cap-radius
bound for a projected unit direction. -/
theorem projected_norm_lt_of_not_transverse
    {n : ℕ} (u v : Kakeya.Space n) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (θ p : ℝ) (hθ : 0 < θ) (hp : 0 ≤ p)
    (hPyth : ⟪u, v⟫_ℝ ^ 2 + p ^ 2 = 1)
    (hNot : ¬ TransverseDirections u v θ) :
    p < θ := by
  have hsin := unit_sine_sq_lt_of_not_transverse u v hu hv θ hθ.le hNot
  nlinarith

/-- The near-direction cap radius follows from a Pythagorean projected
coordinate, using the original tube directions. -/
theorem original_nontransverse_projected_norm_le
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (θ : ℝ) (hθ : 0 < θ)
    (hUnit : ∀ r : T, ‖direction r‖ = 1)
    (hPyth : ∀ r i : T,
      ⟪direction r, direction i⟫_ℝ ^ 2 + ‖projection r i‖ ^ 2 = 1) :
    ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ := by
  intro r i hi
  have hnot : ¬ TransverseDirections (direction r) (direction i) θ := by
    simpa only [nonTransverseDirectionIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  exact (projected_norm_lt_of_not_transverse
    (direction r) (direction i) (hUnit r) (hUnit i)
    θ ‖projection r i‖ hθ (norm_nonneg _) (hPyth r i) hnot).le

end Kakeya.Ninety21
