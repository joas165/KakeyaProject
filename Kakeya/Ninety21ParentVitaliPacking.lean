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



/-- The selected Vitali balls satisfy the numerical packing estimate of
Lemma 4.4 when each original tube has length at most one and the canonical
localization radii satisfy `δ ≤ R ≤ 1`. -/
theorem ConcreteGreedyVitaliCandidates.selected_card_le_of_originalTube_geometry
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2))
    (δ A : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun r => Kakeya.unitTube (center r) (direction r) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun r => Kakeya.unitTube (center r) (direction r) δ) g)
    (hv : ∀ r, direction r ≠ 0)
    (hNorm : ∀ r, ‖direction r‖ ≤ 1)
    (hA : 0 < A)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hδR : ∀ m, δ ≤ d.radius m)
    (hRone : ∀ m, d.radius m ≤ 1)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (hr : r ∈ g.B m) :
    ((d.selected m r).card : ℝ) ≤
      ((7 * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
        (packingBallConstant (k + 2) * A)) *
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
  let R := d.radius m
  have hR : 0 < R := d.hRadius m
  have hDisjoint :
      (↑(d.selected m r) : Set (Fin (g.ballCount m))).PairwiseDisjoint
        (fun i => Metric.ball (d.centers m i) R) := by
    intro i hi j hj hij
    have h := d.selected_disjoint m r hr i hi j hj hij
    simpa only [d.hBall m i, d.hBall m j] using h
  have hHit (i : Fin (g.ballCount m)) (hi : i ∈ d.selected m r) :
      (Metric.ball (d.centers m i) R ∩
        Kakeya.unitTube (center r) (direction r) δ).Nonempty := by
    simpa only [d.hBall m i] using
      (d.selected_ball_meets_parent_tube m r hr i hi)
  have hVolume := originalTube_disjoint_balls_real_volume_le k
    (center r) (direction r) δ R (d.centers m) (d.selected m r)
    (hv r) (hNorm r) hR (hδR m) hDisjoint hHit
  have hScale :
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) * R = A := by
    dsimp [R]
    rw [hRadius m]
    exact canonicalGreedyVitaliRadius_scale (T := T) (k + 2) A m
  exact disjoint_balls_card_le_dyadic k (d.selected m r).card
    R A (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (packingBallConstant (k + 2)) (packingBallConstant (k + 1))
    hR (hRone m) hA (Kakeya.Eighty4.dyadicScale_pos _ m)
    (packingBallConstant_pos _) (packingBallConstant_pos _).le
    hScale hVolume

/-- Tube-wise Euclidean packing supplies the parent-associated `hHallRight`
without an independent selected-family incidence hypothesis. -/
theorem ConcreteGreedyVitaliCandidates.parent_associated_hHallRight_of_geometry
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2))
    (δ A : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun r => Kakeya.unitTube (center r) (direction r) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun r => Kakeya.unitTube (center r) (direction r) δ) g)
    (hv : ∀ r, direction r ≠ 0)
    (hNorm : ∀ r, ‖direction r‖ ≤ 1)
    (hA : 0 < A)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hδR : ∀ m, δ ≤ d.radius m)
    (hRone : ∀ m, d.radius m ≤ 1) :
    ∀ m r,
      (∑ i : Fin (d.retained.ballCount m),
        if (∃ s : ({t : T // t ∈ d.retained.B m} ⊕
            {p : T × ℕ // p ∈ d.retained.P m}),
          d.retained.tubeOf m s = r ∧ d.retained.ballOf m s = i)
        then (1 : ℝ) else 0) ≤
          ((7 * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
            (packingBallConstant (k + 2) * A)) *
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
            ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
  let K : ℝ :=
    (7 * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
      (packingBallConstant (k + 2) * A)
  have hK : 0 ≤ K := by
    have hωn := packingBallConstant_pos (k + 2)
    have hωtrans := packingBallConstant_pos (k + 1)
    dsimp [K]
    positivity
  exact d.parent_associated_hHallRight (k + 2) K hK
    (fun m r hr => d.selected_card_le_of_originalTube_geometry
      center direction δ A g (hv := hv) (hNorm := hNorm) hA
      hRadius hδR hRone m r hr)



/-- Euclidean tube–ball bounds with the parent-associated incidence derived
from the original-tube Vitali packing estimate. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanTubeBallBounds_of_geometry
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
    (hNorm : ∀ j, ‖direction j‖ ≤ 1)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hδR : ∀ m, δ ≤ d.radius m)
    (hRone : ∀ m, d.radius m ≤ 1)
    (hCenters : ∀ m i,
      d.centers m i ∈ Kakeya.Eighty4.concreteDyadicBand
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hScale : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        (Fintype.card T : ℝ))
    (hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hNormCount : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z) :
    ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained := by
  let K : ℝ := (7 * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
    (packingBallConstant (k + 2) * A)
  have hK : 0 ≤ K := by
    have hωn := packingBallConstant_pos (k + 2)
    have hωtrans := packingBallConstant_pos (k + 1)
    dsimp [K]
    positivity
  have hRadius' : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) := by
    intro m
    exact hRadius m
  exact d.euclideanTubeBallBounds_of_selected_packing
    μ center direction δ hδ g hT hv hDom A C Z K hA.le hC hK
    hCgeom hRadius' hCenters hScale hSelected hNormCount
    (fun m r hr => d.selected_card_le_of_originalTube_geometry
      center direction δ A g hv hNorm hA hRadius hδR hRone m r hr)

end Kakeya.Ninety21
