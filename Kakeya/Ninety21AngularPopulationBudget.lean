module

public import Kakeya.Ninety21AngularProjectionPacking

/-!
# Angular-cap population normalization

A quantitative spherical-cap bound and the lower normalization for the
number of directions imply the near-direction budget used in transverse
incidence counting.
-/

@[expose] public section

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- A small fixed angular aperture gives a population budget when the
separated family has the expected lower cardinality. -/
theorem angular_population_real_bound
    (d : ℕ) (ε θ c N : ℝ)
    (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hSmall : 8 * (5 : ℝ) ^ d * θ ^ d ≤ c)
    (hNorm : c ≤ N * ε ^ d) :
    8 * (1 + 4 * θ / ε) ^ d ≤ N := by
  have hθ : 0 ≤ θ := le_trans hε.le hεθ
  have hBase : 1 + 4 * θ / ε ≤ 5 * θ / ε := by
    apply (le_div_iff₀ hε).2
    have hId : (1 + 4 * θ / ε) * ε = ε + 4 * θ := by
      field_simp [ne_of_gt hε]
      <;> ring
    rw [hId]
    nlinarith
  have hPow : (1 + 4 * θ / ε) ^ d ≤ (5 * θ / ε) ^ d := by
    have hBaseNonneg : 0 ≤ 1 + 4 * θ / ε := by positivity
    exact pow_le_pow_left₀ hBaseNonneg hBase d
  have hScaled :
      8 * (1 + 4 * θ / ε) ^ d * ε ^ d ≤ N * ε ^ d := by
    calc
      8 * (1 + 4 * θ / ε) ^ d * ε ^ d
          ≤ 8 * (5 * θ / ε) ^ d * ε ^ d := by
            have h8 := mul_le_mul_of_nonneg_left hPow (show (0 : ℝ) ≤ 8 by norm_num)
            exact mul_le_mul_of_nonneg_right h8 (pow_nonneg hε.le d)
      _ = 8 * (5 * θ) ^ d := by
            rw [div_pow]
            field_simp [ne_of_gt (pow_pos hε d)]
      _ = 8 * (5 : ℝ) ^ d * θ ^ d := by rw [mul_pow]; ring
      _ ≤ c := hSmall
      _ ≤ N * ε ^ d := hNorm
  by_contra hGoal
  have hStrict : N < 8 * (1 + 4 * θ / ε) ^ d := lt_of_not_ge hGoal
  have hContradiction :
      N * ε ^ d < 8 * (1 + 4 * θ / ε) ^ d * ε ^ d :=
    mul_lt_mul_of_pos_right hStrict (pow_pos hε d)
  exact (not_lt_of_ge hScaled) hContradiction

/-- An explicit cap-count bound implies the near-direction cardinality
hypothesis, using only original direction indices. -/
theorem nonTransverseDirectionIndices_budget_of_quantitative_packing
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n) (ε θ c : ℝ)
    (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hCap : ∀ r : T,
      ((nonTransverseDirectionIndices direction θ r).card : ℝ) ≤
        2 * (1 + 4 * θ / ε) ^ (n - 1))
    (hSmall : 8 * (5 : ℝ) ^ (n - 1) * θ ^ (n - 1) ≤ c)
    (hPopulation : c ≤ (Fintype.card T : ℝ) * ε ^ (n - 1)) :
    ∀ r : T,
      4 * (nonTransverseDirectionIndices direction θ r).card ≤
        Fintype.card T := by
  have hReal := angular_population_real_bound (n - 1) ε θ c
    (Fintype.card T : ℝ) hε hεθ hSmall hPopulation
  intro r
  have hCast :
      4 * ((nonTransverseDirectionIndices direction θ r).card : ℝ) ≤
        (Fintype.card T : ℝ) := by
    nlinarith [hCap r]
  exact_mod_cast hCast

/-- The exceptional-piece budget with an explicit quantitative cap
packing estimate in place of the abstract near-direction population bound. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_cap_packing
    {n : ℕ} {T : Type*} [Fintype T]
    (μ : MeasureTheory.Measure (Kakeya.Space n))
    (center direction : T → Kakeya.Space n)
    (δ θ ε c : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n d.retained)
    (hθ : 0 < θ) (hε : 0 < ε) (hεθ : ε ≤ θ)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hCap : ∀ r : T,
      ((nonTransverseDirectionIndices direction θ r).card : ℝ) ≤
        2 * (1 + 4 * θ / ε) ^ (n - 1))
    (hSmall : 8 * (5 : ℝ) ^ (n - 1) * θ ^ (n - 1) ≤ c)
    (hPopulation : c ≤ (Fintype.card T : ℝ) * ε ^ (n - 1))
    (hParentSelected : ∀ m r,
      r ∈ (d.retained.toBallLocalized μ n b).B m → r ∈ g.B m) :
    ∃ L : ℕ, ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      δ ≤ d.radius m →
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ
          (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n
          (d.retained.toBallLocalized μ n b).toRetainedDyadicData m).card : ℝ) ≤
        8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  have hNear := nonTransverseDirectionIndices_budget_of_quantitative_packing
    direction ε θ c hε hεθ hCap hSmall hPopulation
  exact d.exceptional_scaled_budget_uniform_cover
    μ center direction δ θ g b hθ hUnit
    (fun _ r => nonTransverseDirectionIndices direction θ r)
    (fun _ r _ => hNear r)
    hParentSelected
    (fun _ r _ ell hEll =>
      transverse_of_not_mem_nonTransverseDirectionIndices
        direction θ r ell hEll)

end Kakeya.Ninety21
