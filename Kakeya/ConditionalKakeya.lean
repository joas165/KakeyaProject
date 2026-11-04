module
public import Mathlib

/-!
# Conditional Kakeya estimates

Finite tube multiplicity, measurable mass, and moment estimates under explicit
level-budget hypotheses.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Conditional

section Measure

variable {X : Type*} [MeasurableSpace X]

variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def chi (E : Set X) : X → ℝ := by
  classical
  exact E.indicator (fun _ => 1)

noncomputable def mass (E : Set X) : ℝ := ∫ x, chi E x ∂μ

lemma chi_nonneg (E : Set X) (x : X) : 0 ≤ chi E x := by
  classical
  by_cases hx : x ∈ E <;> simp [chi, Set.indicator, hx]

lemma chi_integrable (E : Set X) (hE : MeasurableSet E) :
    Integrable (chi E) μ := (integrable_const (1 : ℝ)).indicator hE

/-- A finite cover gives the volume upper bound; disjointness is unnecessary. -/
theorem mass_le_sum {P : Type*} [Fintype P]
    (F : Set X) (E : P → Set X)
    (hF : MeasurableSet F) (hE : ∀ p, MeasurableSet (E p))
    (hcover : ∀ x ∈ F, ∃ p, x ∈ E p) :
    mass μ F ≤ ∑ p, mass μ (E p) := by
  classical
  have hs : Integrable (fun x => ∑ p, chi (E p) x) μ := by
    apply integrable_finsetSum
    intro p hp
    exact chi_integrable μ (E p) (hE p)
  have hpoint : ∀ x, chi F x ≤ ∑ p, chi (E p) x := by
    intro x
    by_cases hx : x ∈ F
    · obtain ⟨p, hp⟩ := hcover x hx
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset P)) (f := fun r => chi (E r) x)
        (fun r _ => chi_nonneg (E r) x) (Finset.mem_univ p)
      simpa [chi, Set.indicator_of_mem hx, Set.indicator_of_mem hp] using h
    · simpa [chi, Set.indicator_of_notMem hx] using
        (Finset.sum_nonneg (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
          chi_nonneg (E p) x))
  calc
    mass μ F ≤ ∫ x, ∑ p, chi (E p) x ∂μ :=
      integral_mono_ae (chi_integrable μ F hF) hs (Filter.Eventually.of_forall hpoint)
    _ = ∑ p, mass μ (E p) := by
      exact integral_finsetSum Finset.univ (fun p _ => chi_integrable μ (E p) (hE p))


theorem moment_from_level_budgets {J : Type*} [Fintype J]
    (f : X → ℝ) (F : J → Set X) (q : J → ℝ) (p H : ℝ)
    (hp : 0 < p) (hf : ∀ x, 0 ≤ f x)
    (hInt : Integrable (fun x => f x ^ p) μ)
    (hF : ∀ j, MeasurableSet (F j)) (hq : ∀ j, 0 < q j)
    (hcover : ∀ x, f x = 0 ∨ ∃ j, x ∈ F j ∧ f x ≤ 2 * q j)
    (hlevel : ∀ j, q j ^ p * mass μ (F j) ≤ H) :
    (∫ x, f x ^ p ∂μ) ≤ (2 : ℝ) ^ p * H * (Fintype.card J : ℝ) := by
  classical
  let g : J → X → ℝ := fun j x => (2 : ℝ) ^ p * q j ^ p * chi (F j) x
  have hg : ∀ j, Integrable (g j) μ := by
    intro j
    exact (chi_integrable μ (F j) (hF j)).const_mul _
  have hsum : Integrable (fun x => ∑ j, g j x) μ := by
    apply integrable_finsetSum
    intro j hj
    exact hg j
  have hnonneg : ∀ j x, 0 ≤ g j x := by
    intro j x
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (hq j).le _)) (chi_nonneg (F j) x)
  have hpoint : ∀ x, f x ^ p ≤ ∑ j, g j x := by
    intro x
    rcases hcover x with hz | ⟨j, hx, hfx⟩
    · rw [hz, Real.zero_rpow (ne_of_gt hp)]
      exact Finset.sum_nonneg (fun j _ => hnonneg j x)
    · have hpow : f x ^ p ≤ (2 * q j) ^ p :=
        Real.rpow_le_rpow (hf x) hfx hp.le
      have hterm : f x ^ p ≤ g j x := by
        simpa [g, chi, Set.indicator_of_mem hx,
          Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) (hq j).le] using hpow
      exact hterm.trans (Finset.single_le_sum
        (fun r (_ : r ∈ (Finset.univ : Finset J)) => hnonneg r x)
        (Finset.mem_univ j))
  calc
    (∫ x, f x ^ p ∂μ) ≤ ∫ x, ∑ j, g j x ∂μ :=
      integral_mono_ae hInt hsum (Filter.Eventually.of_forall hpoint)
    _ = ∑ j, ∫ x, g j x ∂μ :=
      integral_finsetSum Finset.univ (fun j _ => hg j)
    _ = ∑ j, (2 : ℝ) ^ p * (q j ^ p * mass μ (F j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [g, mass, integral_const_mul]
      ring
    _ ≤ ∑ _j : J, (2 : ℝ) ^ p * H := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hlevel j) (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ p * H * (Fintype.card J : ℝ) := by simp [mul_comm]

theorem norm_of_moment_bound (f : X → ℝ) (p H : ℝ)
    (hp : 0 < p)
    (hbound : (∫ x, f x ^ p ∂μ) ≤ H)
    (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ^ p ∂μ) ^ (1 / p) ≤ H ^ (1 / p) := by
  exact Real.rpow_le_rpow
    (integral_nonneg (fun x => Real.rpow_nonneg (hf x) p))
    hbound (by positivity)

end Measure

theorem dimension_exponents (n : ℕ) (hn : 2 ≤ n) :
    1 + (1 : ℝ) / ((n : ℝ) - 1) = (n : ℝ) / ((n : ℝ) - 1) ∧
    1 / (1 + (1 : ℝ) / ((n : ℝ) - 1)) = ((n : ℝ) - 1) / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hfirst : 1 + (1 : ℝ) / ((n : ℝ) - 1) =
      (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp [hd]
    <;> ring
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  field_simp [hd, hn0]

end Kakeya.Conditional
