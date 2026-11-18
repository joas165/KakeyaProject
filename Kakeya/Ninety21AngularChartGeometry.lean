module

public import Kakeya.Ninety21AngularPopulationBudget

/-!
# Unit spherical-cap chart estimates

The axial coordinate of a unit vector is Lipschitz with respect to its
transverse coordinate on either of the two caps of transverse radius `1/2`.
-/

@[expose] public section

namespace Kakeya.Ninety21

/-- Axial coordinates of unit vectors in the same spherical cap vary by
at most the distance between their transverse coordinate norms. -/
theorem unit_cap_axial_difference_le
    (a b A B D : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ≤ 1 / 2) (hB : B ≤ 1 / 2)
    (hUnitA : a ^ 2 + A ^ 2 = 1)
    (hUnitB : b ^ 2 + B ^ 2 = 1)
    (hSide : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0))
    (hNormDiff : |A - B| ≤ D) :
    |a - b| ≤ D := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hNormDiff
  have hAQuarter : A ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hA0 (show 0 ≤ (1 / 2 : ℝ) - A by linarith)]
  have hBQuarter : B ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hB0 (show 0 ≤ (1 / 2 : ℝ) - B by linarith)]
  have hAax : (3 / 4 : ℝ) ≤ a ^ 2 := by linarith
  have hBax : (3 / 4 : ℝ) ≤ b ^ 2 := by linarith
  have hAxialSum : 1 ≤ |a + b| := by
    rcases hSide with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have haHalf : (1 / 2 : ℝ) ≤ a := by
        by_contra h
        have hprod : 0 ≤ a * ((1 / 2 : ℝ) - a) :=
          mul_nonneg ha (by linarith)
        nlinarith
      have hbHalf : (1 / 2 : ℝ) ≤ b := by
        by_contra h
        have hprod : 0 ≤ b * ((1 / 2 : ℝ) - b) :=
          mul_nonneg hb (by linarith)
        nlinarith
      rw [abs_of_nonneg (by linarith : 0 ≤ a + b)]
      linarith
    · have haHalf : a ≤ -(1 / 2 : ℝ) := by
        by_contra h
        have hprod : 0 ≤ (-a) * ((1 / 2 : ℝ) + a) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hbHalf : b ≤ -(1 / 2 : ℝ) := by
        by_contra h
        have hprod : 0 ≤ (-b) * ((1 / 2 : ℝ) + b) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      rw [abs_of_nonpos (by linarith : a + b ≤ 0)]
      linarith
  have hNormDiff' : |B - A| ≤ D := by
    simpa only [abs_sub_comm] using hNormDiff
  have hNormSum0 : 0 ≤ B + A := by linarith
  have hNormSum1 : B + A ≤ 1 := by linarith
  have hSqBound : |a ^ 2 - b ^ 2| ≤ D := by
    have hW : |B ^ 2 - A ^ 2| ≤ D := by
      calc
        |B ^ 2 - A ^ 2| = |B - A| * (B + A) := by
          rw [show B ^ 2 - A ^ 2 = (B - A) * (B + A) by ring,
            abs_mul, abs_of_nonneg hNormSum0]
        _ ≤ D * (B + A) :=
          mul_le_mul_of_nonneg_right hNormDiff' hNormSum0
        _ ≤ D := by
          nlinarith [mul_nonneg hD0
            (show 0 ≤ 1 - (B + A) by linarith)]
    have heq : a ^ 2 - b ^ 2 = B ^ 2 - A ^ 2 := by linarith
    rw [heq]
    exact hW
  calc
    |a - b| ≤ |a - b| * |a + b| := by
      nlinarith [mul_nonneg (abs_nonneg (a - b))
        (show 0 ≤ |a + b| - 1 by linarith)]
    _ = |a ^ 2 - b ^ 2| := by
      rw [← abs_mul, show (a - b) * (a + b) = a ^ 2 - b ^ 2 by ring]
    _ ≤ D := hSqBound

/-- A Pythagorean two-cap chart satisfies the reverse Lipschitz condition
required by the angular projection counting theorem. -/
theorem unit_two_cap_reverse_lipschitz
    {n : ℕ} {T : Type*}
    (direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (axial : T → T → ℝ)
    (side : T → T → Bool)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθHalf : θ ≤ 1 / 2)
    (near : T → T → Prop)
    (hPyth : ∀ r i : T,
      (axial r i) ^ 2 + ‖projection r i‖ ^ 2 = 1)
    (hSmall : ∀ r i : T, near r i → ‖projection r i‖ ≤ θ)
    (hSameSide : ∀ r i j : T, side r i = side r j →
      (0 ≤ axial r i ∧ 0 ≤ axial r j) ∨
      (axial r i ≤ 0 ∧ axial r j ≤ 0))
    (hCoordDist : ∀ r i j : T,
      dist (direction i) (direction j) ≤
        dist (projection r i) (projection r j) +
        |axial r i - axial r j|) :
    ∀ r i j : T, near r i → near r j →
      side r i = side r j →
      dist (direction i) (direction j) ≤
        2 * dist (projection r i) (projection r j) := by
  intro r i j hi hj hside
  have hNormi : ‖projection r i‖ ≤ 1 / 2 :=
    (hSmall r i hi).trans hθHalf
  have hNormj : ‖projection r j‖ ≤ 1 / 2 :=
    (hSmall r j hj).trans hθHalf
  have hNormDiff :
      |‖projection r i‖ - ‖projection r j‖| ≤
        dist (projection r i) (projection r j) := by
    simpa only [dist_eq_norm] using
      (abs_norm_sub_norm_le (projection r i) (projection r j))
  have hAxial : |axial r i - axial r j| ≤
      dist (projection r i) (projection r j) :=
    unit_cap_axial_difference_le
      (axial r i) (axial r j)
      ‖projection r i‖ ‖projection r j‖
      (dist (projection r i) (projection r j))
      (norm_nonneg _) (norm_nonneg _)
      hNormi hNormj (hPyth r i) (hPyth r j)
      (hSameSide r i j hside) hNormDiff
  have hDist := hCoordDist r i j
  linarith


/-- The two-chart cardinal estimate with the reverse Lipschitz condition
obtained from the Pythagorean decomposition of unit directions. -/
theorem nonTransverseDirectionIndices_card_of_unit_chart_geometry
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (axial : T → T → ℝ)
    (side : T → T → Bool)
    (ε θ : ℝ) (hε : 0 < ε) (hθ0 : 0 ≤ θ) (hθHalf : θ ≤ 1 / 2)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hPyth : ∀ r i : T,
      (axial r i) ^ 2 + ‖projection r i‖ ^ 2 = 1)
    (hProjSmall : ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ)
    (hSameSide : ∀ r i j : T, side r i = side r j →
      (0 ≤ axial r i ∧ 0 ≤ axial r j) ∨
      (axial r i ≤ 0 ∧ axial r j ≤ 0))
    (hCoordDist : ∀ r i j : T,
      dist (direction i) (direction j) ≤
        dist (projection r i) (projection r j) +
        |axial r i - axial r j|) :
    ∃ L : ℕ, ∀ r : T,
      (nonTransverseDirectionIndices direction θ r).card ≤ 2 * L := by
  have hReverse := unit_two_cap_reverse_lipschitz
    direction projection axial side θ hθ0 hθHalf
    (fun r i => i ∈ nonTransverseDirectionIndices direction θ r)
    hPyth hProjSmall hSameSide hCoordDist
  exact nonTransverseDirectionIndices_card_of_projected_charts
    direction projection side ε θ hε hθ0
    hSeparated hProjSmall hReverse

end Kakeya.Ninety21
