module
public import Mathlib
public import Kakeya.ConditionalKakeya

/-!
# Dyadic level budgets

Relates incidence counts, localized mass, and geometric piece estimates.
-/

@[expose] public section

open scoped BigOperators

namespace Kakeya.Eighty9

variable {ι : Type*}

theorem localized_mass_le_card
    (D : Finset ι) (mass : ι → ℝ) (level H V : ℝ)
    (hH : 0 ≤ H)
    (hCapture : level ≤ H * (∑ k ∈ D, mass k))
    (hPiece : ∀ k ∈ D, mass k ≤ V) :
    level ≤ H * ((D.card : ℝ) * V) := by
  classical
  have hsum : (∑ k ∈ D, mass k) ≤ (D.card : ℝ) * V := by
    calc
      (∑ k ∈ D, mass k) ≤ ∑ _k ∈ D, V := by
        apply Finset.sum_le_sum
        intro k hk
        exact hPiece k hk
      _ = (D.card : ℝ) * V := by simp
  exact hCapture.trans (mul_le_mul_of_nonneg_left hsum hH)

theorem localized_level_scaled_bound
    (D : Finset ι) (mass : ι → ℝ)
    (level H V q N : ℝ) (hH : 0 ≤ H) (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hCapture : level ≤ H * (∑ k ∈ D, mass k))
    (hPiece : ∀ k ∈ D, mass k ≤ V)
    (hCount : q * (D.card : ℝ) ≤ 2 * N) :
    q * level ≤ 2 * H * N * V := by
  have hMass := localized_mass_le_card D mass level H V hH hCapture hPiece
  have hCountV := mul_le_mul_of_nonneg_right hCount hV
  have hBound := mul_le_mul_of_nonneg_left hCountV hH
  calc
    q * level ≤ q * (H * ((D.card : ℝ) * V)) :=
      mul_le_mul_of_nonneg_left hMass hq
    _ = H * ((q * (D.card : ℝ)) * V) := by ring
    _ ≤ H * ((2 * N) * V) := hBound
    _ = 2 * H * N * V := by ring

theorem localized_level_normalized_bound
    (D : Finset ι) (mass : ι → ℝ)
    (level H C deltaPow R q N Z : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hdeltaPow : 0 ≤ deltaPow) (hq : 0 ≤ q)
    (hCapture : level ≤ H * (∑ k ∈ D, mass k))
    (hPiece : ∀ k ∈ D, mass k ≤ C * deltaPow * R)
    (hCount : q * (D.card : ℝ) ≤ 2 * N)
    (hNormalization : N * deltaPow ≤ Z) :
    q * level ≤ 2 * H * C * Z * R := by
  have hV : 0 ≤ C * deltaPow * R := by positivity
  have hScaled := localized_level_scaled_bound
    D mass level H (C * deltaPow * R) q N
    hH hV hq hCapture hPiece hCount
  have hcoef : 0 ≤ 2 * H * C * R := by positivity
  have hNormScaled := mul_le_mul_of_nonneg_left hNormalization hcoef
  calc
    q * level ≤ 2 * H * N * (C * deltaPow * R) := hScaled
    _ = (2 * H * C * R) * (N * deltaPow) := by ring
    _ ≤ (2 * H * C * R) * Z := hNormScaled
    _ = 2 * H * C * Z * R := by ring

end Kakeya.Eighty9
