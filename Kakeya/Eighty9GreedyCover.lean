module
public import Kakeya.ConditionalKakeya
public import Kakeya.GreedyDecay

/-!
The mass-capture argument from Eighty4GreedyCover.lean, with only
its actual proof dependencies retained. It derives mass capture from a
one-step greedy residual inequality and a localized cover of the gained
union. The cover and one-step recurrence remain explicit hypotheses.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Kakeya.Eighty4
/-- The actual region gained by the first `k` greedy steps. -/
def greedyUnion {X : Type*} (Q : ℕ → Set X) (k : ℕ) : Set X :=
  ⋃ i ∈ Finset.range k, Q i

/-- The finite greedy union is measurable whenever each gained piece is. -/
theorem greedyUnion_measurable
    {X : Type*} [MeasurableSpace X]
    (Q : ℕ → Set X) (hQ : ∀ k, MeasurableSet (Q k)) (K : ℕ) :
    MeasurableSet (greedyUnion Q K) := by
  unfold greedyUnion
  exact MeasurableSet.iUnion (fun i =>
    MeasurableSet.iUnion (fun _ => hQ i))

/-- Volume of the uncovered part of a measurable level set. -/
noncomputable def greedyResidual
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set X) (Q : ℕ → Set X) (k : ℕ) : ℝ :=
  Conditional.mass μ (F \ greedyUnion Q k)

/-- Finite-measure mass conservation for the disjoint decomposition
`F = U ∪ (F \\ U)`, valid when `U ⊆ F`. -/
theorem mass_eq_covered_add_residual
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F U : Set X)
    (hF : MeasurableSet F) (hU : MeasurableSet U)
    (hSub : U ⊆ F) :
    Conditional.mass μ F =
      Conditional.mass μ U + Conditional.mass μ (F \ U) := by
  have hchi : (fun x => Conditional.chi F x) =
      (fun x => Conditional.chi U x + Conditional.chi (F \ U) x) := by
    funext x
    by_cases hxU : x ∈ U
    · have hxF : x ∈ F := hSub hxU
      have hxD : x ∉ F \ U := by
        intro hd
        exact hd.2 hxU
      simp [Conditional.chi, hxU, hxF, hxD]
    · by_cases hxF : x ∈ F
      · have hxD : x ∈ F \ U := ⟨hxF, hxU⟩
        simp [Conditional.chi, hxU, hxF, hxD]
      · have hxD : x ∉ F \ U := by
          intro hd
          exact hxF hd.1
        simp [Conditional.chi, hxU, hxF, hxD]
  unfold Conditional.mass
  rw [hchi]
  exact integral_add
    (Conditional.chi_integrable μ U hU)
    (Conditional.chi_integrable μ (F \ U) (hF.diff hU))

/-- If the trimmed localized pieces cover `U`, finite subadditivity
bounds the covered mass by the sum of masses of the SAME pieces.
No disjointness assumption on the trimmed pieces is used. -/
theorem mass_le_trimmed_sum_of_cover
    {X T : Type*} [MeasurableSpace X]
    [Fintype T] [DecidableEq T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (E G : T → Set X) (D : Finset T)
    (hU : MeasurableSet U)
    (hPieces : ∀ j ∈ D, MeasurableSet (E j ∩ G j))
    (hCover : U ⊆ ⋃ j ∈ D, E j ∩ G j) :
    Conditional.mass μ U ≤
      ∑ j ∈ D, Conditional.mass μ (E j ∩ G j) := by
  classical
  let P : {j // j ∈ D} → Set X := fun j => E j.val ∩ G j.val
  have hCover' : ∀ x ∈ U, ∃ j : {j // j ∈ D}, x ∈ P j := by
    intro x hx
    obtain ⟨j, hjx⟩ := Set.mem_iUnion.mp (hCover hx)
    obtain ⟨hj, hp⟩ := Set.mem_iUnion.mp hjx
    exact ⟨⟨j, hj⟩, hp⟩
  have hsum : Conditional.mass μ U ≤
      ∑ j : {j // j ∈ D}, Conditional.mass μ (P j) :=
    Conditional.mass_le_sum μ U P hU
      (fun j => hPieces j.val j.property) hCover'
  calc
    Conditional.mass μ U ≤
        ∑ j : {j // j ∈ D}, Conditional.mass μ (P j) := hsum
    _ = ∑ j ∈ D.attach, Conditional.mass μ (E j.val ∩ G j.val) := rfl
    _ = ∑ j ∈ D, Conditional.mass μ (E j ∩ G j) := by
      exact Finset.sum_attach D (fun j => Conditional.mass μ (E j ∩ G j))

/-- The mass-capture inequality from Theorem 4.1 and the user's
*greedy-union cover* hypothesis, not assumed as a separate volume bound.

The one-step inequality is exactly the numerical greedy estimate for
residual volumes; it is the only greedy-dynamics premise. -/
theorem mass_capture_from_greedy_union
    {X T : Type*} [MeasurableSpace X]
    [Fintype T] [DecidableEq T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set X) (Q : ℕ → Set X)
    (E G : T → Set X) (D : Finset T)
    (q N : ℝ)
    (hq : 0 < q) (hqN : q ≤ N)
    (hF : MeasurableSet F)
    (hU : MeasurableSet (greedyUnion Q ⌈N / q⌉₊))
    (hSub : greedyUnion Q ⌈N / q⌉₊ ⊆ F)
    (hStep : ∀ k, greedyResidual μ F Q (k + 1) ≤
      (1 - q / N) * greedyResidual μ F Q k)
    (hPieces : ∀ j ∈ D, MeasurableSet (E j ∩ G j))
    (hCover : greedyUnion Q ⌈N / q⌉₊ ⊆
      ⋃ j ∈ D, E j ∩ G j) :
    Conditional.mass μ F ≤
      (1 / (1 - Real.exp (-1))) *
        (∑ j ∈ D, Conditional.mass μ (E j ∩ G j)) := by
  let R : ℕ → ℝ := fun k => greedyResidual μ F Q k
  have hR0 : R 0 = Conditional.mass μ F := by
    simp [R, greedyResidual, greedyUnion]
  have hRnonneg : 0 ≤ R 0 := by
    rw [hR0]
    exact integral_nonneg (fun x => Conditional.chi_nonneg F x)
  have hRstep : ∀ k, R (k + 1) ≤ (1 - q / N) * R k := hStep
  have hGreedy :=
    (greedy_capture_from_recurrence R q N hq hqN hRnonneg hRstep).2
  rw [hR0] at hGreedy
  have hSplit : Conditional.mass μ F =
      Conditional.mass μ (greedyUnion Q ⌈N / q⌉₊) + R ⌈N / q⌉₊ := by
    simpa only [R, greedyResidual] using
      (mass_eq_covered_add_residual μ F (greedyUnion Q ⌈N / q⌉₊)
        hF hU hSub)
  have hMajor : Conditional.mass μ F ≤
      (1 / (1 - Real.exp (-1))) *
        Conditional.mass μ (greedyUnion Q ⌈N / q⌉₊) := by
    have hCancel : Conditional.mass μ F - R ⌈N / q⌉₊ =
        Conditional.mass μ (greedyUnion Q ⌈N / q⌉₊) := by
      linarith
    simpa only [hCancel] using hGreedy
  have hCoefficient : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have hExp : Real.exp (-1) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr hExp.le)
  have hSum := mass_le_trimmed_sum_of_cover μ
    (greedyUnion Q ⌈N / q⌉₊) E G D hU hPieces hCover
  exact hMajor.trans (mul_le_mul_of_nonneg_left hSum hCoefficient)


end Kakeya.Eighty4
