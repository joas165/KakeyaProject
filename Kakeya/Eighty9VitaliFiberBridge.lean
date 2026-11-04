module
public import Kakeya.Eighty9FiniteVitali

/-!
The finite Vitali theorem yields an actual tube-indexed selection.
No bound |S j| ≤ 1 is claimed. In particular, this does NOT discharge
any lower incidence hypothesis of the full conditional Kakeya theorem.
-/

@[expose] public section

namespace Kakeya.Eighty9

variable {T I X : Type*} [MetricSpace X]

/-- Run finite equal-radius Vitali separately for every tube. -/
theorem exists_tubeWise_equal_radius_vitali
    (B : Finset T) (L : T → Finset I)
    (b : T → I → X) (R : ℝ) (hR : 0 < R) :
    ∃ S : T → Finset I,
      (∀ j ∈ B, S j ⊆ L j) ∧
      (∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (Metric.ball (b j i) R) (Metric.ball (b j i') R)) ∧
      (∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
        Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) := by
  classical
  have hChoice : ∀ j : T, ∃ Sj : Finset I,
      Sj ⊆ L j ∧
      (∀ i ∈ Sj, ∀ i' ∈ Sj, i ≠ i' →
        Disjoint (Metric.ball (b j i) R) (Metric.ball (b j i') R)) ∧
      (∀ i ∈ L j, ∃ d ∈ Sj,
        Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) := by
    intro j
    exact Kakeya.exists_disjoint_equal_balls_cover (L j) (b j) R hR
  let S : T → Finset I := fun j => Classical.choose (hChoice j)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro j hj
    exact (Classical.choose_spec (hChoice j)).1
  · intro j hj
    exact (Classical.choose_spec (hChoice j)).2.1
  · intro j hj
    exact (Classical.choose_spec (hChoice j)).2.2

/-- For nonempty original fibers, each selected fiber is nonempty. -/
theorem tubeWise_vitali_nonempty_fibers
    (B : Finset T) (L S : T → Finset I)
    (b : T → I → X) (R : ℝ)
    (hL : ∀ j ∈ B, (L j).Nonempty)
    (hCover : ∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
      Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) :
    ∀ j ∈ B, (S j).Nonempty := by
  intro j hj
  obtain ⟨i, hi⟩ := hL j hj
  obtain ⟨d, hd, _⟩ := hCover j hj i hi
  exact ⟨d, hd⟩

end Kakeya.Eighty9
