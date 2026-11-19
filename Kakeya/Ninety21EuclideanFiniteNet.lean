module

public import Kakeya.Ninety21ExceptionalTransverseBudget

/-!
# Uniform Euclidean finite nets

Compactness gives a finite half-radius net for a fixed closed ball. Scaling and
translation give a covering cardinal independent of the center and radius.
The covering constant is used in the transverse exceptional-piece estimate.
-/

@[expose] public section

namespace Kakeya.Ninety21

/-- A Euclidean closed ball of radius `D * R` has a finite open-ball cover
of radius `R / 2`, with cardinal bounded independently of `R` and its center. -/
theorem euclidean_uniform_half_radius_net
    (n : ℕ) (D : ℝ) (_hD : 0 ≤ D) :
    ∃ L : ℕ, ∀ (R : ℝ), 0 < R → ∀ c : Kakeya.Space n,
      ∃ Z : Finset (Kakeya.Space n), Z.card ≤ L ∧
        ∀ x : Kakeya.Space n, dist x c ≤ D * R →
          ∃ z ∈ Z, dist x z < R / 2 := by
  classical
  have hCompact : IsCompact (Metric.closedBall (0 : Kakeya.Space n) D) :=
    isCompact_closedBall _ _
  obtain ⟨S, _hS, hFinite, hCover⟩ :=
    hCompact.finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2)
  let A : Finset (Kakeya.Space n) := hFinite.toFinset
  refine ⟨A.card, ?_⟩
  intro R hR c
  let f : Kakeya.Space n → Kakeya.Space n := fun z => c + R • z
  refine ⟨A.image f, Finset.card_image_le, ?_⟩
  intro x hx
  let y : Kakeya.Space n := R⁻¹ • (x - c)
  have hXY : x = c + R • y := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
    abel
  have hNorm : ‖y‖ = ‖x - c‖ / R := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    ring
  have hxNorm : ‖x - c‖ ≤ D * R := by
    simpa only [dist_eq_norm] using hx
  have hy : y ∈ Metric.closedBall (0 : Kakeya.Space n) D := by
    change dist y (0 : Kakeya.Space n) ≤ D
    simpa only [dist_zero_right, hNorm] using (div_le_iff₀ hR).2 hxNorm
  have hCoverAtY :
      ∃ z : Kakeya.Space n, ∃ _hz : z ∈ S,
        y ∈ Metric.ball z ((1 : ℝ) / 2) := by
    simpa only [Set.mem_iUnion] using hCover hy
  obtain ⟨z, hzS, hzBall⟩ := hCoverAtY
  have hzA : z ∈ A := hFinite.mem_toFinset.mpr hzS
  have hyz : dist y z < (1 : ℝ) / 2 := Metric.mem_ball.mp hzBall
  have hScale : dist (c + R • y) (c + R • z) = R * dist y z := by
    calc
      dist (c + R • y) (c + R • z) = ‖R • (y - z)‖ := by
        rw [dist_eq_norm]
        congr 1
        rw [smul_sub]
        abel
      _ = R * dist y z := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, dist_eq_norm]
  refine ⟨f z, Finset.mem_image.mpr ⟨z, hzA, rfl⟩, ?_⟩
  calc
    dist x (f z) = R * dist y z := by
      rw [hXY]
      exact hScale
    _ < R * ((1 : ℝ) / 2) := mul_lt_mul_of_pos_left hyz hR
    _ = R / 2 := by ring

/-- The finite-net constant for two transverse tubes depends only on
Euclidean dimension and the quantitative transversality parameter. -/
theorem euclidean_transverse_uniform_half_radius_net
    (n : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ L : ℕ, ∀ (R : ℝ), 0 < R → ∀ c : Kakeya.Space n,
      ∃ Z : Finset (Kakeya.Space n), Z.card ≤ L ∧
        ∀ x : Kakeya.Space n,
          dist x c ≤ (4 + 8 / θ) * R →
            ∃ z ∈ Z, dist x z < R / 2 := by
  exact euclidean_uniform_half_radius_net n (4 + 8 / θ) (by positivity)

/-- The exceptional-piece budget for the actual retained greedy–Vitali
family, with the Euclidean covering-number hypothesis discharged. The same
constant applies at every dyadic level. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_uniform_cover
    {n : ℕ} {T : Type*} [Fintype T]
    (μ : MeasureTheory.Measure (Kakeya.Space n))
    (center direction : T → Kakeya.Space n)
    (δ θ : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n d.retained)
    (hθ : 0 < θ)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (near : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → Finset T)
    (hNear : ∀ m r, r ∈ (d.retained.toBallLocalized μ n b).B m →
      4 * (near m r).card ≤ Fintype.card T)
    (hParentSelected : ∀ m r, r ∈ (d.retained.toBallLocalized μ n b).B m →
      r ∈ g.B m)
    (hTransverse : ∀ m r, r ∈ (d.retained.toBallLocalized μ n b).B m →
      ∀ ell ∉ near m r,
        TransverseDirections (direction r) (direction ell) θ) :
    ∃ L : ℕ, ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      δ ≤ d.radius m →
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ
          (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n
          (d.retained.toBallLocalized μ n b).toRetainedDyadicData m).card : ℝ) ≤
        8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  obtain ⟨L, hCover⟩ := euclidean_transverse_uniform_half_radius_net n θ hθ
  refine ⟨L, ?_⟩
  intro m hδR
  exact d.exceptional_scaled_budget_of_transverse_geometry
    μ center direction δ θ L g b m hδR hθ hUnit (near m)
    (hNear m) (hParentSelected m) (hTransverse m)
    (hCover (d.radius m) (d.hRadius m))

end Kakeya.Ninety21
