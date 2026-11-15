module

public import Kakeya.Ninety21OccupiedVitaliPieces
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Greedy Vitali selection and the two-radius retained family

A finite radius-R localization of the selected greedy gains gives a tube-wise
Vitali subfamily. Occupancy, disjointness, and triple-radius coverage follow
from that selection. The retained family uses the original radius-R ball
indices, while the analytic cover uses their triple-radius enlargements.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- A relatively compact gain has a finite radius-R cover whose centers
belong to that gain. Every such candidate ball is occupied. -/
theorem exists_finite_occupied_radius_cover
    {X : Type*} [MetricSpace X] (s : Set X) (R : ℝ)
    (hR : 0 < R) (hCompact : IsCompact (closure s)) :
    ∃ C : Finset X,
      (∀ c ∈ C, c ∈ s) ∧
      s ⊆ ⋃ c ∈ C, Metric.ball c R := by
  classical
  have hHalf : 0 < R / 2 := by linarith
  let ε : NNReal := ⟨R / 2, le_of_lt hHalf⟩
  have hε : ε ≠ 0 := by
    intro h
    have hz : (ε : ℝ) = 0 := congrArg (fun z : NNReal => (z : ℝ)) h
    have hcoe : (ε : ℝ) = R / 2 := rfl
    rw [hcoe] at hz
    linarith
  obtain ⟨N, hNs, hFinite, hCover⟩ :=
    Metric.exists_finite_isCover_of_isCompact_closure hε hCompact
  refine ⟨hFinite.toFinset, ?_, ?_⟩
  · intro c hc
    exact hNs ((Set.Finite.mem_toFinset hFinite).mp hc)
  · intro x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
      ((Metric.IsCover.subset_iUnion_closedBall hCover) hx)
    obtain ⟨hcN, hxc⟩ := Set.mem_iUnion.mp hc
    have hDist : dist x c ≤ (ε : ℝ) := Metric.mem_closedBall.mp hxc
    have hStrict : dist x c < R := by
      have hcoe : (ε : ℝ) = R / 2 := rfl
      rw [hcoe] at hDist
      linarith
    exact Set.mem_iUnion.mpr ⟨c,
      Set.mem_iUnion.mpr ⟨(Set.Finite.mem_toFinset hFinite).mpr hcN,
        Metric.mem_ball.mpr hStrict⟩⟩

/-- Select occupied Vitali balls from a finite localization of the actual
ordered greedy gains. -/
theorem ConcreteTubeBallGeometry.exists_greedy_occupied_vitali
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (centers : Fin (g.ballCount m) → X)
    (hBall : ∀ i, g.ball m i = Metric.ball (centers i) R)
    (L : (m' : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) →
      T → Finset (Fin (g.ballCount m')))
    (hStages : ∀ k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k)
    (hLocal : ∀ j ∈ g.B m,
      g.gain m j ⊆ ⋃ i ∈ L m j, g.ball m i) :
    ∃ S : T → Finset (Fin (g.ballCount m)),
      (∀ j ∈ g.B m,
        S j ⊆ g.occupiedVitaliIndices L m j) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j,
        (g.gain m j ∩ g.ball m i).Nonempty) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (g.ball m i) (g.ball m i')) ∧
      (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
        ⋃ j ∈ g.B m, ⋃ i ∈ S j,
          tubes j ∩ Metric.ball (centers i) (3 * R)) := by
  classical
  let U := Kakeya.Eighty4.greedyUnion (g.greedyQ m)
    ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊
  have hOriginal : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ L m j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ g.ball m i) := by
    intro x hx
    change x ∈ ⋃ k ∈ Finset.range
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.greedyQ m k at hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hkRange, hxGain⟩ := Set.mem_iUnion.mp hk
    obtain ⟨hj, hStage⟩ := hStages k (Finset.mem_range.mp hkRange)
    have hxParent : x ∈ g.gain m (g.chosen m k) := by
      simpa [ConcreteTubeBallGeometry.gain, hj, hStage,
        ConcreteTubeBallGeometry.greedyQ] using hxGain
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (hLocal (g.chosen m k) hj hxParent)
    obtain ⟨hiL, hxBall⟩ := Set.mem_iUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨g.chosen m k,
      Set.mem_iUnion.mpr ⟨hj,
        Set.mem_iUnion.mpr ⟨i,
          Set.mem_iUnion.mpr ⟨hiL, ?_⟩⟩⟩⟩
    exact ⟨⟨⟨g.gain_subset_parentTube m (g.chosen m k) hxParent,
      hxParent⟩,
      g.gain_subset_dyadicLevel m (g.chosen m k) hxParent⟩,
      hxBall⟩
  have hOccupiedCover :=
    g.occupiedCandidates_cover L m U hOriginal
  have hOccupiedMetric : U ⊆ ⋃ j ∈ g.B m,
      ⋃ i ∈ g.occupiedVitaliIndices L m j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
        Metric.ball (centers i) R) := by
    simpa only [hBall] using hOccupiedCover
  obtain ⟨S, hSub, hDisjoint, hTriple⟩ :=
    exists_concrete_vitali_localized_cover
      (g.B m) (fun j => g.occupiedVitaliIndices L m j)
      (fun (_ : T) i => centers i) R hR
      tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
      U hOccupiedMetric
  refine ⟨S, hSub, ?_, ?_, ?_⟩
  · intro j hj i hi
    exact g.occupiedVitali_nonempty L m j i (hSub j hj hi)
  · intro j hj i hi i' hi' hne
    simpa only [hBall] using hDisjoint j hj i hi i' hi' hne
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hTriple hx)
    obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
    obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hjB,
        Set.mem_iUnion.mpr ⟨i,
          Set.mem_iUnion.mpr ⟨hiS, ⟨hxi.1.1.1, hxi.2⟩⟩⟩⟩⟩

/-- Relatively compact greedy gains admit an occupied, tube-wise disjoint
radius-R Vitali selection whose triple-radius enlargements cover the actual
greedy union. The centers are geometric points, before finite reindexing. -/
theorem ConcreteTubeBallGeometry.exists_greedy_vitali_from_compact_gains
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hStages : ∀ k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k)
    (hCompact : ∀ j ∈ g.B m, IsCompact (closure (g.gain m j))) :
    ∃ S : T → Finset X,
      (∀ j ∈ g.B m, ∀ c ∈ S j, c ∈ g.gain m j) ∧
      (∀ j ∈ g.B m, ∀ c ∈ S j, ∀ c' ∈ S j, c ≠ c' →
        Disjoint (Metric.ball c R) (Metric.ball c' R)) ∧
      (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
        ⋃ j ∈ g.B m, ⋃ c ∈ S j,
          tubes j ∩ Metric.ball c (3 * R)) := by
  classical
  have hCandidates (j : T) :
      ∃ C : Finset X,
        (∀ c ∈ C, c ∈ g.gain m j) ∧
        g.gain m j ⊆ ⋃ c ∈ C, Metric.ball c R := by
    by_cases hj : j ∈ g.B m
    · exact exists_finite_occupied_radius_cover
        (g.gain m j) R hR (hCompact j hj)
    · refine ⟨∅, ?_, ?_⟩
      · intro c hc
        simp at hc
      · simp [ConcreteTubeBallGeometry.gain, hj]
  choose L hL using hCandidates
  let U := Kakeya.Eighty4.greedyUnion (g.greedyQ m)
    ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊
  have hOriginal : U ⊆ ⋃ j ∈ g.B m, ⋃ c ∈ L j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ Metric.ball c R) := by
    intro x hx
    change x ∈ ⋃ k ∈ Finset.range
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.greedyQ m k at hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hkRange, hxGain⟩ := Set.mem_iUnion.mp hk
    obtain ⟨hj, hStage⟩ := hStages k (Finset.mem_range.mp hkRange)
    have hxParent : x ∈ g.gain m (g.chosen m k) := by
      simpa [ConcreteTubeBallGeometry.gain, hj, hStage,
        ConcreteTubeBallGeometry.greedyQ] using hxGain
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
      ((hL (g.chosen m k)).2 hxParent)
    obtain ⟨hcL, hxc⟩ := Set.mem_iUnion.mp hc
    refine Set.mem_iUnion.mpr ⟨g.chosen m k,
      Set.mem_iUnion.mpr ⟨hj,
        Set.mem_iUnion.mpr ⟨c,
          Set.mem_iUnion.mpr ⟨hcL, ?_⟩⟩⟩⟩
    exact ⟨⟨⟨g.gain_subset_parentTube m (g.chosen m k) hxParent,
      hxParent⟩,
      g.gain_subset_dyadicLevel m (g.chosen m k) hxParent⟩,
      hxc⟩
  obtain ⟨S, hSubset, hDisjoint, hTriple⟩ :=
    exists_concrete_vitali_localized_cover (g.B m) L
      (fun (_ : T) c => c) R hR
      tubes (g.gain m) (Kakeya.Eighty4.concreteDyadicBand tubes m)
      U hOriginal
  refine ⟨S, ?_, hDisjoint, ?_⟩
  · intro j hj c hc
    exact (hL j).1 c (hSubset j hj hc)
  · intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hTriple hx)
    obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hj
    obtain ⟨hcS, hxc⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hjB,
        Set.mem_iUnion.mpr ⟨c,
          Set.mem_iUnion.mpr ⟨hcS, ⟨hxc.1.1.1, hxc.2⟩⟩⟩⟩⟩

/-- Finite initial localizations of all dyadic greedy gains. -/
structure ConcreteGreedyVitaliCandidates
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X) (g : ConcreteTubeBallGeometry tubes) where
  radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ
  hRadius : ∀ m, 0 < radius m
  centers : ∀ m, Fin (g.ballCount m) → X
  hBall : ∀ m i, g.ball m i = Metric.ball (centers m i) (radius m)
  candidates : ∀ m, T → Finset (Fin (g.ballCount m))
  hStages : ∀ m k,
    k < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
    g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k
  hLocal : ∀ m j, j ∈ g.B m →
    g.gain m j ⊆ ⋃ i ∈ candidates m j, g.ball m i

/-- A selected Vitali family exists at each dyadic level. -/
theorem ConcreteGreedyVitaliCandidates.exists_selected
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    ∃ S : T → Finset (Fin (g.ballCount m)),
      (∀ j ∈ g.B m,
        S j ⊆ g.occupiedVitaliIndices d.candidates m j) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j,
        (g.gain m j ∩ g.ball m i).Nonempty) ∧
      (∀ j ∈ g.B m, ∀ i ∈ S j, ∀ i' ∈ S j, i ≠ i' →
        Disjoint (g.ball m i) (g.ball m i')) ∧
      (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
        ⋃ j ∈ g.B m, ⋃ i ∈ S j,
          tubes j ∩ Metric.ball (d.centers m i) (3 * d.radius m)) := by
  exact g.exists_greedy_occupied_vitali m (d.radius m) (d.hRadius m)
    (d.centers m) (d.hBall m) d.candidates
    (d.hStages m) (d.hLocal m)

/-- The occupied Vitali selection at every dyadic level. -/
noncomputable def ConcreteGreedyVitaliCandidates.selected
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g) :
    ∀ m, T → Finset (Fin (g.ballCount m)) :=
  fun m => Classical.choose (d.exists_selected m)

/-- Selected balls are occupied and remain disjoint within each tube. -/
theorem ConcreteGreedyVitaliCandidates.selected_occupied
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m)
    (i : Fin (g.ballCount m)) (hi : i ∈ d.selected m j) :
    (g.gain m j ∩ g.ball m i).Nonempty := by
  exact (Classical.choose_spec (d.exists_selected m)).2.1 j hj i hi

theorem ConcreteGreedyVitaliCandidates.selected_disjoint
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m)
    (i : Fin (g.ballCount m)) (hi : i ∈ d.selected m j)
    (i' : Fin (g.ballCount m)) (hi' : i' ∈ d.selected m j)
    (hne : i ≠ i') :
    Disjoint (g.ball m i) (g.ball m i') := by
  exact (Classical.choose_spec (d.exists_selected m)).2.2.1
    j hj i hi i' hi' hne

theorem ConcreteGreedyVitaliCandidates.selected_triple_cover
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ j ∈ g.B m, ⋃ i ∈ d.selected m j,
        tubes j ∩ Metric.ball (d.centers m i) (3 * d.radius m) := by
  exact (Classical.choose_spec (d.exists_selected m)).2.2.2

/-- Retained labels are formed directly from the occupied selected balls. -/
noncomputable def ConcreteGreedyVitaliCandidates.retained
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g) :
    ConcreteTubeBallGeometry tubes :=
  g.withOccupiedVitaliPieces d.selected

/-- The triple-radius cover transfers to exactly the retained label family. -/
theorem ConcreteGreedyVitaliCandidates.retained_triple_cover
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ j ∈ d.retained.B m, ⋃ i ∈ d.retained.coverIndices m j,
        tubes j ∩ Metric.ball (d.centers m i) (3 * d.radius m) := by
  exact g.occupiedVitali_cover_transfer d.selected m
    (fun j i => tubes j ∩ Metric.ball (d.centers m i) (3 * d.radius m))
    (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (fun j hj i hi => d.selected_occupied m j hj i hi)
    (d.selected_triple_cover m)

/-- Every label in the retained family denotes a nonempty radius-R piece. -/
theorem ConcreteGreedyVitaliCandidates.retained_piece_nonempty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ d.retained.B m} ⊕
      {p : T × ℕ // p ∈ d.retained.P m}) :
    (d.retained.piece m s).Nonempty := by
  exact g.withOccupiedVitaliPieces_nonempty d.selected m s

/-- Each retained radius-R ball uses the same index and set as the original
candidate family; no auxiliary tube indices are created. -/
theorem ConcreteGreedyVitaliCandidates.retained_ball_eq
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin (g.ballCount m)) :
    d.retained.ball m i = g.ball m i := rfl

/-- Radius-R incidence counting remains unchanged by the retained-label
construction. In particular, any bound on these incidences transfers verbatim. -/
theorem ConcreteGreedyVitaliCandidates.retained_incidence_eq
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (r : T) :
    (∑ i : Fin (d.retained.ballCount m),
      if (d.retained.ball m i ∩ tubes r).Nonempty then (1 : ℝ) else 0) =
    (∑ i : Fin (g.ballCount m),
      if (g.ball m i ∩ tubes r).Nonempty then (1 : ℝ) else 0) := rfl

/-- The number of distinct selected radius-R balls meeting an original tube
is at most the number of indexed candidate balls meeting that tube. -/
theorem ConcreteGreedyVitaliCandidates.selected_incidence_card_le_all
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (r : T) :
    ((Finset.univ : Finset (Fin (g.ballCount m))).filter (fun i =>
      (∃ j ∈ g.B m, i ∈ d.selected m j) ∧
        (g.ball m i ∩ tubes r).Nonempty)).card ≤
    ((Finset.univ : Finset (Fin (g.ballCount m))).filter (fun i =>
      (g.ball m i ∩ tubes r).Nonempty)).card := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.2⟩

/-- The finite label budget applies to the Vitali-selected retained family. -/
theorem ConcreteGreedyVitaliCandidates.retained_index_budget
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (∑ j ∈ d.retained.B m, ((d.retained.coverIndices m j).card : ℝ)) ≤
      ((d.retained.B m).card : ℝ) + ((d.retained.P m).card : ℝ) := by
  exact d.retained.coverIndices_card_budget m

/-- Populate the two-radius analytic endpoint from the selected Vitali family.
The initial local finite covers and the greedy stage correspondence are the
only covering premises. -/
noncomputable def ConcreteTwoRadiusGreedy.ofGreedyVitaliCandidates
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (b : ConcreteTubeBallBounds μ tubes n d.retained)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hStep : ∀ m k,
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k)
    (hTripleCost : ∀ m j i,
      j ∈ d.retained.B m → i ∈ d.retained.coverIndices m j →
      Kakeya.Conditional.mass μ
        (tubes j ∩ Metric.ball (d.centers m i)
          (3 * twoRadiusRadius d.retained b m)) ≤
      b.C * b.deltaPow * twoRadiusRadius d.retained b m) :
    ConcreteTwoRadiusGreedy μ tubes n d.retained b := by
  exact ConcreteTwoRadiusGreedy.ofOccupiedVitali μ tubes n g d.selected b
    hT hStep d.centers
    (by
      intro m i
      calc
        g.ball m i = Metric.ball (d.centers m i) (d.radius m) :=
          d.hBall m i
        _ = Metric.ball (d.centers m i)
          (twoRadiusRadius d.retained b m) := by rw [hRadius m])
    (fun m j hj i hi => d.selected_occupied m j hj i hi)
    (by
      intro m
      have hCover := d.selected_triple_cover m
      rw [hRadius m] at hCover
      simpa only [ConcreteGreedyVitaliCandidates.retained] using hCover)
    hTripleCost

end Kakeya.Ninety21
