module
public import Mathlib

/-!
Finite equal-radius Vitali selection extracted from Kakeya/Covering.lean.
It gives disjoint R-balls and a cover by 3R-balls; the 3R-balls
are NOT asserted to be disjoint.
-/

@[expose] public section

namespace Kakeya
section EqualRadius

variable {X ι : Type*} [MetricSpace X]

/-- A finite family admits a 2r-separated subfamily whose centers are
within distance strictly less than 2r of all original centers. -/
theorem exists_separated_centers_cover
    (I : Finset ι) (b : ι → X) (r : ℝ) (hr : 0 < r) :
    ∃ J : Finset ι, J ⊆ I ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j → 2 * r ≤ dist (b i) (b j)) ∧
      (∀ i ∈ I, ∃ j ∈ J, dist (b i) (b j) < 2 * r) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · simp
      · simp
  | @insert a I ha ih =>
      obtain ⟨J, hJI, hsep, hcover⟩ := ih
      by_cases hnear : ∃ j ∈ J, dist (b a) (b j) < 2 * r
      · refine ⟨J, ?_, hsep, ?_⟩
        · intro i hi
          exact Finset.mem_insert_of_mem (hJI hi)
        · intro i hi
          rcases Finset.mem_insert.mp hi with hia | hiI
          · subst i
            exact hnear
          · exact hcover i hiI
      · have hfar : ∀ j ∈ J, 2 * r ≤ dist (b a) (b j) := by
          intro j hj
          by_contra h
          exact hnear ⟨j, hj, lt_of_not_ge h⟩
        refine ⟨insert a J, ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with hia | hiJ
          · subst i
            exact Finset.mem_insert_self a I
          · exact Finset.mem_insert_of_mem (hJI hiJ)
        · intro i hi j hj hij
          rcases Finset.mem_insert.mp hi with hia | hiJ
          · subst i
            rcases Finset.mem_insert.mp hj with hja | hjJ
            · exact False.elim (hij hja.symm)
            · exact hfar j hjJ
          · rcases Finset.mem_insert.mp hj with hja | hjJ
            · subst j
              simpa only [dist_comm] using hfar i hiJ
            · exact hsep i hiJ j hjJ hij
        · intro i hi
          rcases Finset.mem_insert.mp hi with hia | hiI
          · subst i
            refine ⟨a, Finset.mem_insert_self a J, ?_⟩
            simpa only [dist_self] using (show (0 : ℝ) < 2 * r by linarith)
          · obtain ⟨j, hj, hd⟩ := hcover i hiI
            exact ⟨j, Finset.mem_insert_of_mem hj, hd⟩

/-- The triangle inequality turns the center-distance bound into 3r coverage. -/
theorem ball_subset_triple_of_dist_lt_two
    (a b : X) (r : ℝ) (hab : dist a b < 2 * r) :
    Metric.ball a r ⊆ Metric.ball b (3 * r) := by
  intro x hx
  change dist x a < r at hx
  change dist x b < 3 * r
  have ht := dist_triangle x a b
  linarith

/-- Equal-radius finite Vitali selection: selected balls are pairwise disjoint;
each original ball is contained in a selected ball enlarged by a factor of 3. -/
theorem exists_disjoint_equal_balls_cover
    (I : Finset ι) (b : ι → X) (r : ℝ) (hr : 0 < r) :
    ∃ J : Finset ι, J ⊆ I ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        Disjoint (Metric.ball (b i) r) (Metric.ball (b j) r)) ∧
      (∀ i ∈ I, ∃ j ∈ J,
        Metric.ball (b i) r ⊆ Metric.ball (b j) (3 * r)) := by
  obtain ⟨J, hJI, hsep, hcover⟩ := exists_separated_centers_cover I b r hr
  refine ⟨J, hJI, ?_, ?_⟩
  · intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    have h := hsep i hi j hj hij
    linarith
  · intro i hi
    obtain ⟨j, hj, hd⟩ := hcover i hi
    exact ⟨j, hj, ball_subset_triple_of_dist_lt_two (b i) (b j) r hd⟩

/-- Only the target set F needs to be covered; no claim is made that the
undilated selected balls cover F. -/
theorem exists_disjoint_equal_balls_cover_target
    (I : Finset ι) (b : ι → X) (r : ℝ) (hr : 0 < r)
    (F : Set X) (hF : F ⊆ ⋃ i ∈ I, Metric.ball (b i) r) :
    ∃ J : Finset ι, J ⊆ I ∧
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
        Disjoint (Metric.ball (b i) r) (Metric.ball (b j) r)) ∧
      F ⊆ ⋃ j ∈ J, Metric.ball (b j) (3 * r) := by
  obtain ⟨J, hJI, hdisj, hcover⟩ := exists_disjoint_equal_balls_cover I b r hr
  refine ⟨J, hJI, hdisj, ?_⟩
  intro x hx
  have hxU := hF hx
  simp only [Set.mem_iUnion] at hxU ⊢
  obtain ⟨i, hi, hxi⟩ := hxU
  obtain ⟨j, hj, hij⟩ := hcover i hi
  exact ⟨j, hj, hij hxi⟩

end EqualRadius
end Kakeya
