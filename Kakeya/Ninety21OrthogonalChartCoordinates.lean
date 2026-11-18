module

public import Kakeya.Ninety21QuantitativeCapPacking

/-!
# Orthogonal coordinates for unit directions

For a unit vector `u` in Euclidean dimension `k+1`, the orthogonal
complement of `u` has an orthonormal coordinate basis with `k` coordinates.
The perpendicular component is represented in this Euclidean space.
-/

@[expose] public section

namespace Kakeya.Ninety21

open scoped InnerProductSpace

/-- The orthogonal complement of a nonzero direction has dimension `k`.
Mathlib constructs its orthonormal basis. -/
noncomputable def directionOrthogonalBasis
    (k : ℕ) (u : Kakeya.Space (k + 1)) (hu : ‖u‖ = 1) :
    OrthonormalBasis (Fin k) ℝ ↥(ℝ ∙ u)ᗮ := by
  have hu0 : u ≠ 0 := by
    intro heq
    simp [heq] at hu
  letI : Fact (Module.finrank ℝ (Kakeya.Space (k + 1)) = k + 1) :=
    ⟨by simp [Kakeya.Space]⟩
  exact OrthonormalBasis.fromOrthogonalSpanSingleton k hu0

/-- The component of a vector perpendicular to a chosen unit direction. -/
noncomputable def unitDirectionPerpendicular
    {k : ℕ} (u v : Kakeya.Space (k + 1)) (hu : ‖u‖ = 1) :
    ↥(ℝ ∙ u)ᗮ :=
  ⟨v - (⟪v, u⟫_ℝ) • u, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have huinner : ⟪u, u⟫_ℝ = 1 := by
      simpa [hu] using (real_inner_self_eq_norm_sq u)
    rw [inner_sub_left, real_inner_smul_left, huinner]
    ring⟩

/-- Concrete orthogonal chart of a unit vector relative to the parent
unit direction. -/
noncomputable def unitDirectionOrthogonalChart
    {k : ℕ} (u v : Kakeya.Space (k + 1)) (hu : ‖u‖ = 1) :
    Kakeya.Space k :=
  (directionOrthogonalBasis k u hu).repr (unitDirectionPerpendicular u v hu)

/-- The chart norm is the norm of the perpendicular component. -/
theorem unitDirectionOrthogonalChart_norm
    {k : ℕ} (u v : Kakeya.Space (k + 1)) (hu : ‖u‖ = 1) :
    ‖unitDirectionOrthogonalChart u v hu‖ =
      ‖v - (⟪v, u⟫_ℝ) • u‖ := by
  change ‖(directionOrthogonalBasis k u hu).repr
      (unitDirectionPerpendicular u v hu)‖ =
    ‖unitDirectionPerpendicular u v hu‖
  exact (directionOrthogonalBasis k u hu).repr.norm_map
    (unitDirectionPerpendicular u v hu)

/-- The norm of the perpendicular component of a unit vector is the
square root of the Gram determinant. -/
theorem unitDirectionOrthogonalChart_pythagoras
    {k : ℕ} (u v : Kakeya.Space (k + 1))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ⟪v, u⟫_ℝ ^ 2 + ‖unitDirectionOrthogonalChart u v hu‖ ^ 2 = 1 := by
  have hnorm := unitDirectionOrthogonalChart_norm u v hu
  have hgram := unit_directions_gram_identity
    u v hu hv (⟪v, u⟫_ℝ) 1
  have hsymm : ⟪u, v⟫_ℝ = ⟪v, u⟫_ℝ := (real_inner_comm u v).symm
  rw [hsymm] at hgram
  have hswap : (⟪v, u⟫_ℝ) • u - (1 : ℝ) • v =
      -(v - (⟪v, u⟫_ℝ) • u) := by
    simp only [one_smul]
    abel
  rw [hswap, norm_neg] at hgram
  rw [← hnorm] at hgram
  nlinarith

end Kakeya.Ninety21
