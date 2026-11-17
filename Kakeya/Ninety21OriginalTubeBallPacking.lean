module
public import Kakeya.Ninety21GreedyVitaliBounds

/-!
# Original-tube localization-ball geometry

A radius-`R` ball meeting a `δ`-tube, with `δ ≤ R`, is contained in
the `3R`-neighborhood of the tube's central segment. A disjoint finite
family of measurable balls satisfies the corresponding volume-sum bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

/-- A radius-`R` ball meeting an original tube lies within distance `3R`
of a point on the central segment of that tube. -/
theorem originalTube_intersecting_ball_subset_axisNeighborhood
    {n : ℕ} (p v b : Kakeya.Space n) (δ R : ℝ)
    (hδR : δ ≤ R)
    (hHit : (Metric.ball b R ∩ Kakeya.unitTube p v δ).Nonempty) :
    Metric.ball b R ⊆
      {y | ∃ t : ℝ, |t| ≤ (1 : ℝ) / 2 ∧
        dist y (p + t • v) < 3 * R} := by
  obtain ⟨x, hxb, hxt⟩ := hHit
  obtain ⟨t, w, ht, _hw, hnorm, hx⟩ := hxt
  subst x
  intro y hy
  refine ⟨t, ht, ?_⟩
  have h1 : dist y b < R := Metric.mem_ball.mp hy
  have h2 : dist b (p + t • v + w) < R := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hxb)
  have h3 : dist (p + t • v + w) (p + t • v) ≤ δ := by
    have heq : (p + t • v + w) - (p + t • v) = w := by
      abel
    simpa only [dist_eq_norm, heq] using hnorm
  have htri : dist y (p + t • v) ≤
      dist y b + dist b (p + t • v + w) +
        dist (p + t • v + w) (p + t • v) := by
    have ha := dist_triangle y b (p + t • v + w)
    have hb := dist_triangle y (p + t • v + w) (p + t • v)
    linarith
  linarith

/-- The sum of the volumes of disjoint measurable localized balls does not
exceed the volume of a set containing them all. -/
theorem disjoint_localization_balls_volume_sum_le
    {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (balls : I → Set X) (s : Finset I) (E : Set X)
    (hd : (↑s : Set I).PairwiseDisjoint balls)
    (hm : ∀ i ∈ s, MeasurableSet (balls i))
    (hsub : ∀ i ∈ s, balls i ⊆ E) :
    (∑ i ∈ s, μ (balls i)) ≤ μ E := by
  have hUnion : (⋃ i ∈ s, balls i) ⊆ E := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact hsub i his hxi
  calc
    (∑ i ∈ s, μ (balls i)) = μ (⋃ i ∈ s, balls i) :=
      (measure_biUnion_finset hd hm).symm
    _ ≤ μ E := measure_mono hUnion

end Kakeya.Ninety21
