module

public import Kakeya.Ninety21OrthogonalChartCoordinates

/-!
# Concrete angular packing for original unit directions

The orthogonal coordinates and Euclidean volume packing yield the quantitative
bound for nontransverse direction indices, used in the exceptional-piece budget.
-/

@[expose] public section

namespace Kakeya.Ninety21

open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable

/-- The hemisphere of a direction relative to a parent unit vector. -/
noncomputable def unitDirectionHemisphere
    {k : ℕ} (u v : Kakeya.Space (k + 1)) : Bool :=
  if 0 ≤ ⟪v, u⟫_ℝ then true else false

/-- Equal hemisphere labels give compatible signs of axial coordinates. -/
theorem unitDirectionHemisphere_same_sign
    {k : ℕ} (u v w : Kakeya.Space (k + 1))
    (h : unitDirectionHemisphere u v = unitDirectionHemisphere u w) :
    (0 ≤ ⟪v, u⟫_ℝ ∧ 0 ≤ ⟪w, u⟫_ℝ) ∨
    (⟪v, u⟫_ℝ ≤ 0 ∧ ⟪w, u⟫_ℝ ≤ 0) := by
  by_cases hv : 0 ≤ ⟪v, u⟫_ℝ
  · by_cases hw : 0 ≤ ⟪w, u⟫_ℝ
    · exact Or.inl ⟨hv, hw⟩
    · simp [unitDirectionHemisphere, hv, hw] at h
  · by_cases hw : 0 ≤ ⟪w, u⟫_ℝ
    · simp [unitDirectionHemisphere, hv, hw] at h
    · exact Or.inr ⟨le_of_lt (lt_of_not_ge hv),
        le_of_lt (lt_of_not_ge hw)⟩

/-- The ambient metric is bounded by the difference of the perpendicular
coordinates plus the axial-coordinate difference. -/
theorem unitDirectionOrthogonalChart_coordinate_distance
    {k : ℕ} (u v w : Kakeya.Space (k + 1)) (hu : ‖u‖ = 1) :
    dist v w ≤
      dist (unitDirectionOrthogonalChart u v hu)
        (unitDirectionOrthogonalChart u w hu) +
      |⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ| := by
  let P := unitDirectionPerpendicular u v hu
  let Q := unitDirectionPerpendicular u w hu
  have hDecomp : v - w =
      (⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ) • u + ((P : Kakeya.Space (k + 1)) - Q) := by
    dsimp [P, Q, unitDirectionPerpendicular]
    rw [sub_smul]
    abel
  have hDistChart :
      dist (unitDirectionOrthogonalChart u v hu)
        (unitDirectionOrthogonalChart u w hu) = ‖P - Q‖ := by
    change dist ((directionOrthogonalBasis k u hu).repr P)
      ((directionOrthogonalBasis k u hu).repr Q) = ‖P - Q‖
    rw [dist_eq_norm, ← map_sub]
    exact (directionOrthogonalBasis k u hu).repr.norm_map (P - Q)
  have hSubtype : ‖P - Q‖ = ‖(P : Kakeya.Space (k + 1)) - Q‖ := by
    rfl
  have hScalar : ‖(⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ) • u‖ =
      |⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ| := by
    rw [norm_smul, hu]
    simp [Real.norm_eq_abs]
  calc
    dist v w = ‖v - w‖ := dist_eq_norm v w
    _ = ‖(⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ) • u +
        ((P : Kakeya.Space (k + 1)) - Q)‖ := by rw [hDecomp]
    _ ≤ ‖(⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ) • u‖ +
        ‖(P : Kakeya.Space (k + 1)) - Q‖ := norm_add_le _ _
    _ = dist (unitDirectionOrthogonalChart u v hu)
        (unitDirectionOrthogonalChart u w hu) +
        |⟪v, u⟫_ℝ - ⟪w, u⟫_ℝ| := by
          rw [hScalar, ← hSubtype, ← hDistChart]
          ring

/-- Quantitative cardinal bound for the original nontransverse directions,
using concrete orthogonal coordinates rather than an abstract chart. -/
theorem original_unit_directions_quantitative_cap_card
    {k : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space (k + 2))
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ) (hθHalf : θ ≤ 1 / 2)
    (hUnit : ∀ r : T, ‖direction r‖ = 1)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j)) :
    ∀ r : T,
      ((nonTransverseDirectionIndices direction θ r).card : ℝ) ≤
        2 * (1 + 4 * θ / ε) ^ (k + 1) := by
  let projection : T → T → Kakeya.Space (k + 1) :=
    fun r i => unitDirectionOrthogonalChart (direction r) (direction i) (hUnit r)
  let axial : T → T → ℝ := fun r i => ⟪direction i, direction r⟫_ℝ
  let side : T → T → Bool :=
    fun r i => unitDirectionHemisphere (direction r) (direction i)
  have hPyth : ∀ r i : T,
      axial r i ^ 2 + ‖projection r i‖ ^ 2 = 1 := by
    intro r i
    exact unitDirectionOrthogonalChart_pythagoras
      (direction r) (direction i) (hUnit r) (hUnit i)
  have hPyth' : ∀ r i : T,
      ⟪direction r, direction i⟫_ℝ ^ 2 + ‖projection r i‖ ^ 2 = 1 := by
    intro r i
    rw [real_inner_comm (direction i) (direction r)]
    exact hPyth r i
  have hSmall := original_nontransverse_projected_norm_le
    direction projection θ hθ hUnit hPyth'
  have hSigns : ∀ r i j : T, side r i = side r j →
      (0 ≤ axial r i ∧ 0 ≤ axial r j) ∨
      (axial r i ≤ 0 ∧ axial r j ≤ 0) := by
    intro r i j hside
    exact unitDirectionHemisphere_same_sign
      (direction r) (direction i) (direction j) hside
  have hDist : ∀ r i j : T,
      dist (direction i) (direction j) ≤
        dist (projection r i) (projection r j) +
        |axial r i - axial r j| := by
    intro r i j
    exact unitDirectionOrthogonalChart_coordinate_distance
      (direction r) (direction i) (direction j) (hUnit r)
  have hReverse := unit_two_cap_reverse_lipschitz
    direction projection axial side θ hθ.le hθHalf
    (fun r i => i ∈ nonTransverseDirectionIndices direction θ r)
    hPyth hSmall hSigns hDist
  exact quantitative_cap_card_of_projected_chart
    direction projection side ε θ hε hθ.le
    hSeparated hSmall hReverse

/-- Exceptional-piece budget from concrete separated unit directions,
with the quantitative lower normalization of the original direction count. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_unit_directions
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : MeasureTheory.Measure (Kakeya.Space (k + 2)))
    (center direction : T → Kakeya.Space (k + 2))
    (δ θ ε c : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2) d.retained)
    (hθ : 0 < θ) (hθHalf : θ ≤ 1 / 2)
    (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hSmall : 8 * (5 : ℝ) ^ (k + 1) * θ ^ (k + 1) ≤ c)
    (hPopulation : c ≤ (Fintype.card T : ℝ) * ε ^ (k + 1))
    (hParentSelected : ∀ m r,
      r ∈ (d.retained.toBallLocalized μ (k + 2) b).B m → r ∈ g.B m) :
    ∃ L : ℕ, ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      δ ≤ d.radius m →
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ
          (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) (k + 2)
          (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData m).card : ℝ) ≤
        8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  have hCap := original_unit_directions_quantitative_cap_card
    direction ε θ hε hθ hθHalf hUnit hSeparated
  exact d.exceptional_scaled_budget_of_cap_packing
    μ center direction δ θ ε c g b hθ hε hεθ hUnit
    hCap hSmall hPopulation hParentSelected

end Kakeya.Ninety21
