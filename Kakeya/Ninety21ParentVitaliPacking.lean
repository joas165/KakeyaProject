module

public import Kakeya.Ninety21OriginalTubeBallPacking

/-!
# Tube-wise incidence for retained Vitali balls

The retained tube–ball labels use indices selected by the Vitali construction
of their parent original tube. Consequently, the associated radius-`R` balls
inherit the tube-wise disjointness of the selected family.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- Every selected radius-`R` Vitali ball intersects its parent original tube. -/
theorem ConcreteGreedyVitaliCandidates.selected_ball_meets_parent_tube
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (hr : r ∈ g.B m)
    (i : Fin (g.ballCount m)) (hi : i ∈ d.selected m r) :
    (g.ball m i ∩ tubes r).Nonempty := by
  obtain ⟨x, hxGain, hxBall⟩ := d.selected_occupied m r hr i hi
  exact ⟨x, hxBall, g.gain_subset_parentTube m r hxGain⟩

/-- Every localization ball associated with a retained label belongs to the
Vitali selection of that label's parent original tube. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_mem_selected
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (i : Fin (d.retained.ballCount m))
    (h : ∃ s : ({t : T // t ∈ d.retained.B m} ⊕
        {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i) :
    i ∈ d.selected m r := by
  obtain ⟨s, hrs, hsi⟩ := h
  have hLabel := g.withOccupiedVitali_label_mem d.selected m s
  have hOcc :=
    (g.mem_occupiedVitaliLabels_iff d.selected m
      (d.retained.tubeOf m s) (d.retained.ballOf m s)).mp hLabel
  have hi : d.retained.ballOf m s ∈
      d.selected m (d.retained.tubeOf m s) :=
    (Finset.mem_filter.mp hOcc.2).1
  rw [hrs, hsi] at hi
  exact hi

/-- The parent of any retained tube–ball label lies in the originally
selected tube family. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_mem_original
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (i : Fin (d.retained.ballCount m))
    (h : ∃ s : ({t : T // t ∈ d.retained.B m} ⊕
        {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i) :
    r ∈ g.B m := by
  obtain ⟨s, hrs, _⟩ := h
  have hLabel := g.withOccupiedVitali_label_mem d.selected m s
  have hMem :=
    (g.mem_occupiedVitaliLabels_iff d.selected m
      (d.retained.tubeOf m s) (d.retained.ballOf m s)).mp hLabel
  simpa only [hrs] using hMem.1

/-- Distinct radius-`R` balls associated with one parent original tube
are disjoint. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_disjoint
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (hr : r ∈ g.B m)
    (i i' : Fin (d.retained.ballCount m))
    (hi : ∃ s : ({t : T // t ∈ d.retained.B m} ⊕
        {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
    (hi' : ∃ s : ({t : T // t ∈ d.retained.B m} ⊕
        {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i')
    (hne : i ≠ i') :
    Disjoint (d.retained.ball m i) (d.retained.ball m i') := by
  have hSelected := d.selected_disjoint m r hr i
    (d.parent_associated_mem_selected m r i hi) i'
    (d.parent_associated_mem_selected m r i' hi') hne
  simpa only [d.retained_ball_eq m i, d.retained_ball_eq m i'] using hSelected

/-- The parent-associated incidence sum is bounded by the cardinality
of the original tube's selected Vitali family. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_count_le_selected
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (r : T) :
    (∑ i : Fin (d.retained.ballCount m),
      if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
          {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
      then (1 : ℝ) else 0) ≤ ((d.selected m r).card : ℝ) := by
  classical
  let I : Finset (Fin (d.retained.ballCount m)) :=
    Finset.univ.filter (fun i =>
      ∃ s : ({t : T // t ∈ d.retained.B m} ⊕
          {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
  have hSub : I ⊆ d.selected m r := by
    intro i hi
    exact d.parent_associated_mem_selected m r i (Finset.mem_filter.mp hi).2
  have hCard : (I.card : ℝ) ≤ ((d.selected m r).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  calc
    (∑ i : Fin (d.retained.ballCount m),
      if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
          {p : T × ℕ // p ∈ d.retained.P m}),
        d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
      then (1 : ℝ) else 0) = (I.card : ℝ) := by
        simp [I, Finset.sum_boole]
    _ ≤ ((d.selected m r).card : ℝ) := hCard

/-- Lemma 4.4's bound on each original tube's selected balls yields
`hHallRight` for the retained tube–ball indexing. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_hHallRight
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hPacking : ∀ m r, r ∈ g.B m →
      ((d.selected m r).card : ℝ) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / ((n : ℝ) - 1))) :
    ∀ m r,
      (∑ i : Fin (d.retained.ballCount m),
        if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
            {p : T × ℕ // p ∈ d.retained.P m}),
          d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
        then (1 : ℝ) else 0) ≤
          K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
            ((1 : ℝ) / ((n : ℝ) - 1)) := by
  classical
  intro m r
  by_cases hr : r ∈ g.B m
  · exact (d.parent_associated_count_le_selected m r).trans (hPacking m r hr)
  · have hNone (i : Fin (d.retained.ballCount m)) :
        ¬ (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
            {p : T × ℕ // p ∈ d.retained.P m}),
          d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i) := by
      intro hi
      exact hr (d.parent_associated_mem_original m r i hi)
    have hZero :
        (∑ i : Fin (d.retained.ballCount m),
          if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
              {p : T × ℕ // p ∈ d.retained.P m}),
            d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
          then (1 : ℝ) else 0) = 0 := by
      simp [hNone]
    rw [hZero]
    exact mul_nonneg hK (Real.rpow_nonneg
      (le_of_lt (Kakeya.Eighty4.dyadicScale_pos _ m)) _)

/-- Construct the concrete bounds using a tube-wise packing estimate for the
selected radius-`R` Vitali balls. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds_of_selected_packing
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z K : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))))
    (hCenters : ∀ m i,
      d.centers m i ∈ Kakeya.Eighty4.concreteDyadicBand
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hScale : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        (Fintype.card T : ℝ))
    (hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z)
    (hPacking : ∀ m r, r ∈ g.B m →
      ((d.selected m r).card : ℝ) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) :
    ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained := by
  exact d.euclideanTubeBallBounds μ center direction δ hδ g hT hv hDom
    A C Z K hA hC hK hCgeom hRadius hCenters hScale hSelected hNorm
    (d.parent_associated_hHallRight (k + 2) K hK hPacking)

end Kakeya.Ninety21
