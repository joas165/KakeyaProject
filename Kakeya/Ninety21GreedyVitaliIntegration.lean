module

public import Kakeya.Ninety21OccupiedVitaliPieces
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Data.Fintype.EquivFin

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

/-- Union of the tubes selected before stage `k`. -/
def prefixTubeUnion {X T : Type*} (tubes : T → Set X)
    (chosen : ℕ → T) (k : ℕ) : Set X :=
  ⋃ i ∈ Finset.range k, tubes (chosen i)

/-- The union of the first `k + 1` selected tubes. -/
theorem prefixTubeUnion_succ {X T : Type*}
    (tubes : T → Set X) (chosen : ℕ → T) (k : ℕ) :
    prefixTubeUnion tubes chosen (k + 1) =
      prefixTubeUnion tubes chosen k ∪ tubes (chosen k) := by
  ext x
  simp only [prefixTubeUnion, Set.mem_iUnion, Finset.mem_range, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact Or.inl ⟨i, h, hx⟩
    · exact Or.inr (by simpa [h] using hx)
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact ⟨k, Nat.lt_succ_self k, hx⟩

/-- Adding one greedy gain extends the greedy union by that gain. -/
theorem greedyUnion_succ {X : Type*} (Q : ℕ → Set X) (k : ℕ) :
    Kakeya.Eighty4.greedyUnion Q (k + 1) =
      Kakeya.Eighty4.greedyUnion Q k ∪ Q k := by
  ext x
  simp only [Kakeya.Eighty4.greedyUnion, Set.mem_iUnion,
    Finset.mem_range, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact Or.inl ⟨i, h, hx⟩
    · exact Or.inr (by simpa [h] using hx)
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact ⟨k, Nat.lt_succ_self k, hx⟩

/-- The greedy gains partition the part of the first tube union in `F`. -/
theorem greedyUnion_concreteGain_eq {X T : Type*}
    (tubes : T → Set X) (F : Set X) (chosen : ℕ → T) (k : ℕ) :
    Kakeya.Eighty4.greedyUnion
      (fun i => Kakeya.Eighty4.concreteGreedyGain tubes F chosen i) k =
        F ∩ prefixTubeUnion tubes chosen k := by
  induction k with
  | zero =>
      simp [Kakeya.Eighty4.greedyUnion, prefixTubeUnion]
  | succ k ih =>
      rw [greedyUnion_succ, ih, prefixTubeUnion_succ]
      change (F ∩ prefixTubeUnion tubes chosen k) ∪
        ((F ∩ tubes (chosen k)) \ prefixTubeUnion tubes chosen k) =
        F ∩ (prefixTubeUnion tubes chosen k ∪ tubes (chosen k))
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      tauto

/-- Residual multiplicity lower-bounds the sum of tube intersections. -/
theorem residual_dyadic_average
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (hT : ∀ j, MeasurableSet (tubes j))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : Set X) (hR : MeasurableSet R)
    (hSub : R ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ R ≤
        ∑ j : T, Kakeya.Conditional.mass μ (R ∩ tubes j) := by
  classical
  have hE (j : T) : MeasurableSet (R ∩ tubes j) :=
    hR.inter (hT j)
  have hIntLeft : Integrable
      (fun x => Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Conditional.chi R x) μ :=
    (Kakeya.Conditional.chi_integrable μ R hR).const_mul _
  have hIntRight : Integrable
      (fun x => ∑ j : T, Kakeya.Conditional.chi (R ∩ tubes j) x) μ := by
    apply integrable_finsetSum
    intro j _
    exact Kakeya.Conditional.chi_integrable μ (R ∩ tubes j) (hE j)
  have hPoint (x : X) :
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Conditional.chi R x ≤
        ∑ j : T, Kakeya.Conditional.chi (R ∩ tubes j) x := by
    by_cases hx : x ∈ R
    · have hSum : (∑ j : T, Kakeya.Conditional.chi (R ∩ tubes j) x) =
          Kakeya.Eighty4.tubeMultiplicity tubes x := by
        unfold Kakeya.Eighty4.tubeMultiplicity
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : x ∈ tubes j
        · simp [Kakeya.Conditional.chi, hx, hj]
        · simp [Kakeya.Conditional.chi, hj]
      rw [hSum]
      simpa [Kakeya.Conditional.chi, hx] using (hSub hx).1
    · have hz (j : T) : x ∉ R ∩ tubes j := fun h => hx h.1
      simp [Kakeya.Conditional.chi, hx, hz]
  calc
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Conditional.mass μ R =
        ∫ x, Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
          Kakeya.Conditional.chi R x ∂μ := by
            simp only [Kakeya.Conditional.mass, integral_const_mul]
    _ ≤ ∫ x, ∑ j : T, Kakeya.Conditional.chi (R ∩ tubes j) x ∂μ :=
      integral_mono_ae hIntLeft hIntRight (Filter.Eventually.of_forall hPoint)
    _ = ∑ j : T, Kakeya.Conditional.mass μ (R ∩ tubes j) := by
      exact integral_finsetSum Finset.univ
        (fun j _ => Kakeya.Conditional.chi_integrable μ (R ∩ tubes j) (hE j))

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

/-- An empty greedy gain contributes no selected Vitali ball. -/
theorem ConcreteGreedyVitaliCandidates.selected_empty_of_gain_empty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m) (hEmpty : g.gain m j = ∅) :
    d.selected m j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨x, hx⟩ := d.selected_occupied m j hj i hi
  have hxGain : x ∈ g.gain m j := hx.1
  rw [hEmpty] at hxGain
  exact hxGain

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

/-- Occupied Vitali reindexing leaves every stage of the greedy sequence unchanged. -/
theorem ConcreteGreedyVitaliCandidates.retained_greedyQ_eq
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    {tubes : T → Set X} {g : ConcreteTubeBallGeometry tubes}
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    d.retained.greedyQ m = g.greedyQ m := by
  funext k
  exact g.withOccupiedVitaliPieces_greedyQ d.selected m k

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



/-- The occupied retained family has the same greedy recurrence as its original
selection, obtained from the maximal-gain averaging inequality. -/
theorem ConcreteGreedyVitaliCandidates.retained_greedy_recurrence_of_average
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hN : 0 < (Fintype.card T : ℝ))
    (hT : ∀ j, MeasurableSet (tubes j))
    (hAverage : ∀ m k,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
        (Fintype.card T : ℝ) *
          Kakeya.Conditional.mass μ (g.greedyQ m k))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (d.retained.greedyQ m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (d.retained.greedyQ m) k := by
  have hStep := g.greedy_recurrence_of_average μ m hN (hAverage m) hT k
  rw [d.retained_greedyQ_eq m]
  exact hStep

/-- The enlarged Vitali cover has the Euclidean tube-ball cost for exactly
the indices represented by the retained family. -/
theorem ConcreteGreedyVitaliCandidates.retained_triple_volume_le
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2)) (δ : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (hv : ∀ j, direction j ≠ 0)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (volume : Measure (Kakeya.Space (k + 2)))
      (Kakeya.Eighty4.greedyUnion (d.retained.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊) ≤
      ∑ j ∈ d.retained.B m, ∑ i ∈ d.retained.coverIndices m j,
        (ENNReal.ofReal (2 * (3 * d.radius m)) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))) := by
  classical
  let U := Kakeya.Eighty4.greedyUnion (d.retained.greedyQ m)
    ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊
  let E : T → Fin (d.retained.ballCount m) →
      Set (Kakeya.Space (k + 2)) := fun j i =>
    Kakeya.unitTube (center j) (direction j) δ ∩
      Metric.ball (d.centers m i) (3 * d.radius m)
  have hCover : U ⊆
      ⋃ j ∈ d.retained.B m, ⋃ i ∈ d.retained.coverIndices m j, E j i := by
    dsimp only [U, E]
    rw [d.retained_greedyQ_eq m]
    exact d.retained_triple_cover m
  change (volume : Measure (Kakeya.Space (k + 2))) U ≤ _
  calc
    _ ≤ (volume : Measure (Kakeya.Space (k + 2)))
        (⋃ j ∈ d.retained.B m,
          ⋃ i ∈ d.retained.coverIndices m j, E j i) :=
        measure_mono hCover
    _ ≤ ∑ j ∈ d.retained.B m,
          ∑ i ∈ d.retained.coverIndices m j,
            (volume : Measure (Kakeya.Space (k + 2))) (E j i) :=
        finite_double_union_measure_le volume
          (d.retained.B m) (d.retained.coverIndices m) E
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact unitTube_tripleBall_volume_le (center j) (direction j)
        (d.centers m i) δ (d.radius m) (hv j) (d.hRadius m).le

/-- Construct the two-radius analytic data from the greedy averaging estimate.
The Vitali cover and retained labels are those selected by `d`. -/
noncomputable def ConcreteTwoRadiusGreedy.ofGreedyVitaliAverage
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (b : ConcreteTubeBallBounds μ tubes n d.retained)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hN : 0 < (Fintype.card T : ℝ))
    (hAverage : ∀ m k,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
        (Fintype.card T : ℝ) *
          Kakeya.Conditional.mass μ (g.greedyQ m k))
    (hTripleCost : ∀ m j i,
      j ∈ d.retained.B m → i ∈ d.retained.coverIndices m j →
      Kakeya.Conditional.mass μ
        (tubes j ∩ Metric.ball (d.centers m i)
          (3 * twoRadiusRadius d.retained b m)) ≤
      b.C * b.deltaPow * twoRadiusRadius d.retained b m) :
    ConcreteTwoRadiusGreedy μ tubes n d.retained b := by
  exact ConcreteTwoRadiusGreedy.ofGreedyVitaliCandidates μ tubes n g d b
    hRadius hT
    (fun m k => g.greedy_recurrence_of_average μ m hN (hAverage m) hT k)
    hTripleCost

/-- The two-radius analytic estimate uses the Theorem 4.6 counting data
of the very same occupied retained tube-ball family. -/
theorem full_conditional_kakeya_of_greedyVitaliAverage
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ) (hn : 2 ≤ n)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (b : ConcreteTubeBallBounds μ tubes n d.retained)
    (a : Paper46LargeLevelInputs μ tubes n
      (d.retained.toBallLocalized μ n b).toRetainedDyadicData)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hN : 0 < (Fintype.card T : ℝ))
    (hAverage : ∀ m k,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
        (Fintype.card T : ℝ) *
          Kakeya.Conditional.mass μ (g.greedyQ m k))
    (hTripleCost : ∀ m j i,
      j ∈ d.retained.B m → i ∈ d.retained.coverIndices m j →
      Kakeya.Conditional.mass μ
        (tubes j ∩ Metric.ball (d.centers m i)
          (3 * twoRadiusRadius d.retained b m)) ≤
      b.C * b.deltaPow * twoRadiusRadius d.retained b m) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46EndpointBudget μ tubes n
          (d.retained.toBallLocalized μ n b).toRetainedDyadicData a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((n : ℝ) - 1) / (n : ℝ)) := by
  exact full_conditional_kakeya_of_paper46_twoRadius μ tubes n hn
    d.retained b
    (ConcreteTwoRadiusGreedy.ofGreedyVitaliAverage μ tubes n g d b
      hRadius hT hN hAverage hTripleCost) a



/-- The transverse unit-ball coefficient in the arbitrary-direction
Euclidean tube–ball volume estimate. -/
noncomputable def tripleRadiusTransverseCoefficient (k : ℕ) : ℝ :=
  (ENNReal.ofReal
    (√Real.pi ^ (k + 1) /
      Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))).toReal

/-- The real mass of a measurable set is its finite measure. -/
theorem conditional_mass_eq_measure_toReal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (E : Set X) (hE : MeasurableSet E) :
    Kakeya.Conditional.mass μ E = (μ E).toReal := by
  simp only [Kakeya.Conditional.mass, Kakeya.Conditional.chi]
  exact MeasureTheory.integral_indicator_one hE

/-- A triple-radius localization has the endpoint cost with the geometric
coefficient absorbed into the same retained-family constant `b.C`. -/
theorem ConcreteGreedyVitaliCandidates.euclidean_triple_cost
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hDeltaPow : b.deltaPow = δ ^ (k + 1))
    (hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (i : Fin (d.retained.ballCount m)) :
    Kakeya.Conditional.mass μ
      (Kakeya.unitTube (center j) (direction j) δ ∩
        Metric.ball (d.centers m i)
          (3 * twoRadiusRadius d.retained b m)) ≤
      b.C * b.deltaPow * twoRadiusRadius d.retained b m := by
  let R := twoRadiusRadius d.retained b m
  let E : Set (Kakeya.Space (k + 2)) :=
    Kakeya.unitTube (center j) (direction j) δ ∩
      Metric.ball (d.centers m i) (3 * R)
  let ω := tripleRadiusTransverseCoefficient k
  have hR : 0 ≤ R := by
    change 0 ≤ twoRadiusRadius d.retained b m
    rw [← hRadius m]
    exact (d.hRadius m).le
  have hE : MeasurableSet E :=
    (hT j).inter Metric.isOpen_ball.measurableSet
  have hMeasured : Kakeya.Conditional.mass μ E = (μ E).toReal :=
    conditional_mass_eq_measure_toReal μ E hE
  have hVolume :
      (volume : Measure (Kakeya.Space (k + 2))) E ≤
        ENNReal.ofReal (2 * (3 * R)) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) := by
    exact unitTube_tripleBall_volume_le
      (center j) (direction j) (d.centers m i) δ R (hv j) hR
  have hReal : (μ E).toReal ≤
      (ENNReal.ofReal (2 * (3 * R)) *
        (ENNReal.ofReal δ ^ (k + 1) *
          ENNReal.ofReal
            (√Real.pi ^ (k + 1) /
              Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1)))).toReal := by
    have hFinite :
        ENNReal.ofReal (2 * (3 * R)) *
          (ENNReal.ofReal δ ^ (k + 1) *
            ENNReal.ofReal
              (√Real.pi ^ (k + 1) /
                Real.Gamma (((k + 1 : ℕ) : ℝ) / 2 + 1))) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      apply ENNReal.mul_ne_top
      · intro ht
        exact ENNReal.ofReal_ne_top (ENNReal.pow_eq_top_iff.mp ht).1
      · exact ENNReal.ofReal_ne_top
    exact ENNReal.toReal_mono hFinite ((hDom E).trans hVolume)
  have hRealBound : (μ E).toReal ≤ (6 * R) * (δ ^ (k + 1) * ω) := by
    have h6R : 0 ≤ 6 * R := by positivity
    rw [show 2 * (3 * R) = 6 * R by ring] at hReal
    simpa only [ω, tripleRadiusTransverseCoefficient,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal h6R, ENNReal.toReal_ofReal hδ] using hReal
  have hNonneg : 0 ≤ R * δ ^ (k + 1) :=
    mul_nonneg hR (pow_nonneg hδ _)
  have hConst : (6 * ω) * (R * δ ^ (k + 1)) ≤
      b.C * (R * δ ^ (k + 1)) :=
    mul_le_mul_of_nonneg_right hCgeom hNonneg
  calc
    Kakeya.Conditional.mass μ E = (μ E).toReal := hMeasured
    _ ≤ (6 * R) * (δ ^ (k + 1) * ω) := hRealBound
    _ = (6 * ω) * (R * δ ^ (k + 1)) := by ring
    _ ≤ b.C * (R * δ ^ (k + 1)) := hConst
    _ = b.C * b.deltaPow * R := by rw [hDeltaPow]; ring

/-! ## Greedy recurrence for selection without replacement -/

/-- The chosen tube maximizes the residual intersection mass among tubes
not selected at earlier stages. -/
def ConcreteTubeBallGeometry.MaximalUnused
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (μ : Measure X) : Prop :=
  ∀ m k j, j ∉ (Finset.range k).image (g.chosen m) →
    Kakeya.Conditional.mass μ
      ((Kakeya.Eighty4.concreteDyadicBand tubes m \
        prefixTubeUnion tubes (g.chosen m) k) ∩ tubes j) ≤
    Kakeya.Conditional.mass μ
      ((Kakeya.Eighty4.concreteDyadicBand tubes m \
        prefixTubeUnion tubes (g.chosen m) k) ∩
        tubes (g.chosen m k))

/-- A finite nonempty set of unused tubes has a maximum residual mass. -/
theorem exists_maximal_unused_tube
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (R : Set X)
    (S : Finset T) (hUnused : (Finset.univ \ S).Nonempty) :
    ∃ j ∈ Finset.univ \ S, ∀ i ∈ Finset.univ \ S,
      Kakeya.Conditional.mass μ (R ∩ tubes i) ≤
        Kakeya.Conditional.mass μ (R ∩ tubes j) := by
  classical
  exact Finset.exists_max_image (Finset.univ \ S)
    (fun i : T => Kakeya.Conditional.mass μ (R ∩ tubes i)) hUnused

/-- The residual mass inequality follows from maximizing over unused tubes.
Previously chosen tubes have empty intersection with the residual. -/
theorem ConcreteTubeBallGeometry.greedy_average_of_maximal_unused
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hMax : g.MaximalUnused μ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k ≤
      (Fintype.card T : ℝ) *
        Kakeya.Conditional.mass μ (g.greedyQ m k) := by
  classical
  let F := Kakeya.Eighty4.concreteDyadicBand tubes m
  let R := F \
    prefixTubeUnion tubes (g.chosen m) k
  have hF : MeasurableSet F :=
    Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m
  have hPrefix : MeasurableSet
      (prefixTubeUnion tubes (g.chosen m) k) := by
    unfold prefixTubeUnion
    exact MeasurableSet.iUnion (fun i =>
      MeasurableSet.iUnion (fun _ => hT (g.chosen m i)))
  have hR : MeasurableSet R := hF.diff hPrefix
  have hMassR :
      Kakeya.Eighty4.greedyResidual μ F (g.greedyQ m) k =
        Kakeya.Conditional.mass μ R := by
    have hUnion : Kakeya.Eighty4.greedyUnion (g.greedyQ m) k =
        F ∩ prefixTubeUnion tubes (g.chosen m) k := by
      change Kakeya.Eighty4.greedyUnion
        (fun i => Kakeya.Eighty4.concreteGreedyGain tubes F (g.chosen m) i) k =
          F ∩ prefixTubeUnion tubes (g.chosen m) k
      exact greedyUnion_concreteGain_eq tubes F (g.chosen m) k
    change Kakeya.Conditional.mass μ
      (F \ Kakeya.Eighty4.greedyUnion (g.greedyQ m) k) =
        Kakeya.Conditional.mass μ R
    rw [hUnion]
    congr 1
    ext x
    change (x ∈ F ∧ ¬ (x ∈ F ∧
      x ∈ prefixTubeUnion tubes (g.chosen m) k)) ↔
      (x ∈ F ∧ ¬ x ∈ prefixTubeUnion tubes (g.chosen m) k)
    tauto
  have hGain : g.greedyQ m k = R ∩ tubes (g.chosen m k) := by
    change (F ∩ tubes (g.chosen m k)) \
      prefixTubeUnion tubes (g.chosen m) k =
        (F \ prefixTubeUnion tubes (g.chosen m) k) ∩
          tubes (g.chosen m k)
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hUpper (j : T) :
      Kakeya.Conditional.mass μ (R ∩ tubes j) ≤
        Kakeya.Conditional.mass μ (R ∩ tubes (g.chosen m k)) := by
    by_cases hj : j ∈ (Finset.range k).image (g.chosen m)
    · obtain ⟨l, hl, hlj⟩ := Finset.mem_image.mp hj
      have hTube : tubes j ⊆
          prefixTubeUnion tubes (g.chosen m) k := by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨l,
          Set.mem_iUnion.mpr ⟨hl, by simpa [hlj] using hx⟩⟩
      have hEmpty : R ∩ tubes j = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hx.1.2 (hTube hx.2)
      have hZero : Kakeya.Conditional.mass μ (R ∩ tubes j) = 0 := by
        rw [hEmpty]
        simp [Kakeya.Conditional.mass, Kakeya.Conditional.chi]
      have hNonneg : 0 ≤ Kakeya.Conditional.mass μ
          (R ∩ tubes (g.chosen m k)) := by
        unfold Kakeya.Conditional.mass
        exact integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg _ x)
      rw [hZero]
      exact hNonneg
    · exact hMax m k j hj
  have hAvg : Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ R ≤
        ∑ j : T, Kakeya.Conditional.mass μ (R ∩ tubes j) :=
    residual_dyadic_average μ tubes hT m R hR (by
      intro x hx
      exact hx.1)
  have hSum : (∑ j : T, Kakeya.Conditional.mass μ (R ∩ tubes j)) ≤
      (Fintype.card T : ℝ) *
        Kakeya.Conditional.mass μ (R ∩ tubes (g.chosen m k)) := by
    calc
      _ ≤ ∑ _j : T,
          Kakeya.Conditional.mass μ (R ∩ tubes (g.chosen m k)) := by
            apply Finset.sum_le_sum
            intro j _
            exact hUpper j
      _ = _ := by simp
  calc
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Eighty4.greedyResidual μ F (g.greedyQ m) k =
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        Kakeya.Conditional.mass μ R := by rw [hMassR]
    _ ≤ ∑ j : T, Kakeya.Conditional.mass μ (R ∩ tubes j) := hAvg
    _ ≤ (Fintype.card T : ℝ) *
        Kakeya.Conditional.mass μ (R ∩ tubes (g.chosen m k)) := hSum
    _ = (Fintype.card T : ℝ) *
        Kakeya.Conditional.mass μ (g.greedyQ m k) := by rw [hGain]

/-- Maximality over unused tubes gives the greedy recurrence for the
original indexed gains, unchanged by occupied Vitali reindexing. -/
theorem ConcreteGreedyVitaliCandidates.retained_greedy_recurrence_of_maximal_unused
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hN : 0 < (Fintype.card T : ℝ))
    (hT : ∀ j, MeasurableSet (tubes j))
    (hMax : g.MaximalUnused μ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (i : ℕ) :
    Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (d.retained.greedyQ m) (i + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (d.retained.greedyQ m) i := by
  exact d.retained_greedy_recurrence_of_average μ tubes g hN hT
    (fun m k => g.greedy_average_of_maximal_unused μ hT hMax m k) m i

/-- Two-radius analytic data from residual maximality over unused tubes
and the Euclidean triple-radius volume cost. -/
noncomputable def ConcreteTwoRadiusGreedy.ofMaximalUnusedVitaliEuclidean
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (hN : 0 < (Fintype.card T : ℝ))
    (hMax : g.MaximalUnused μ)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hDeltaPow : b.deltaPow = δ ^ (k + 1))
    (hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C) :
    ConcreteTwoRadiusGreedy μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained b := by
  exact ConcreteTwoRadiusGreedy.ofGreedyVitaliCandidates μ
    (fun j => Kakeya.unitTube (center j) (direction j) δ)
    (k + 2) g d b hRadius hT
    (fun m i => by
      have h := d.retained_greedy_recurrence_of_maximal_unused
        μ (fun j => Kakeya.unitTube (center j) (direction j) δ)
          g hN hT hMax m i
      rw [d.retained_greedyQ_eq m] at h
      exact h)
    (fun m j i _ _ =>
      d.euclidean_triple_cost μ center direction δ hδ g b hT hv hDom
        hRadius hDeltaPow hCgeom m j i)

/-- The greedy two-radius endpoint uses the same occupied retained
family as the Theorem 4.6 counting data. -/
theorem full_conditional_kakeya_of_maximalUnusedVitaliEuclidean
    {k : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (a : Paper46LargeLevelInputs μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData)
    (hN : 0 < (Fintype.card T : ℝ))
    (hMax : g.MaximalUnused μ)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hDeltaPow : b.deltaPow = δ ^ (k + 1))
    (hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity
      (fun j => Kakeya.unitTube (center j) (direction j) δ) x ^
      (((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ∂μ) ^
      (((((k + 2 : ℕ) : ℝ) - 1) / ((k + 2 : ℕ) : ℝ))) ≤
      ((2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) *
        paper46EndpointBudget μ
          (fun j => Kakeya.unitTube (center j) (direction j) δ)
          (k + 2)
          (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData
          a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((((k + 2 : ℕ) : ℝ) - 1) / ((k + 2 : ℕ) : ℝ))) := by
  exact full_conditional_kakeya_of_paper46_twoRadius μ
    (fun j => Kakeya.unitTube (center j) (direction j) δ)
    (k + 2) (by omega) d.retained b
    (ConcreteTwoRadiusGreedy.ofMaximalUnusedVitaliEuclidean
      μ center direction δ hδ g d b hN hMax hT hv hDom
      hRadius hDeltaPow hCgeom) a

/-! ## Finite center indexing -/

/-- Tube–center pairs, with each center taken from its parent tube's finite net. -/
abbrev VitaliFiniteCenterPair {T X : Type*}
    (B : Finset T) (C : T → Finset X) :=
  Σ j : {j : T // j ∈ B}, {c : X // c ∈ C j.1}

/-- Enumerate the finite tube–center pairs without identifying centers from
    different parent tubes. -/
noncomputable def vitaliFiniteCenterEquiv {T X : Type*}
    (B : Finset T) (C : T → Finset X) :
    Fin (Fintype.card (VitaliFiniteCenterPair B C)) ≃
      VitaliFiniteCenterPair B C := by
  classical
  exact (Fintype.equivFin (VitaliFiniteCenterPair B C)).symm

/-- The parent tube of an enumerated finite-center label. -/
noncomputable def vitaliFiniteParent {T X : Type*}
    (B : Finset T) (C : T → Finset X)
    (i : Fin (Fintype.card (VitaliFiniteCenterPair B C))) : T :=
  ((vitaliFiniteCenterEquiv B C) i).1.1

/-- The center of an enumerated finite-center label. -/
noncomputable def vitaliFiniteCenter {T X : Type*}
    (B : Finset T) (C : T → Finset X)
    (i : Fin (Fintype.card (VitaliFiniteCenterPair B C))) : X :=
  ((vitaliFiniteCenterEquiv B C) i).2.1

/-- The index set associated with one selected parent tube. -/
noncomputable def vitaliFiniteCandidates {T X : Type*}
    (B : Finset T) (C : T → Finset X) (j : T) :
    Finset (Fin (Fintype.card (VitaliFiniteCenterPair B C))) := by
  classical
  exact Finset.univ.filter (fun i => vitaliFiniteParent B C i = j)

/-- Every center in a selected tube's finite net has a unique global pair index. -/
theorem vitaliFinite_index_exists {T X : Type*}
    (B : Finset T) (C : T → Finset X)
    (j : T) (hj : j ∈ B) (c : X) (hc : c ∈ C j) :
    ∃ i : Fin (Fintype.card (VitaliFiniteCenterPair B C)),
      i ∈ vitaliFiniteCandidates B C j ∧
        vitaliFiniteCenter B C i = c := by
  classical
  let p : VitaliFiniteCenterPair B C := ⟨⟨j, hj⟩, ⟨c, hc⟩⟩
  let i := (vitaliFiniteCenterEquiv B C).symm p
  have he : (vitaliFiniteCenterEquiv B C) i = p :=
    (vitaliFiniteCenterEquiv B C).apply_symm_apply p
  have hp : vitaliFiniteParent B C i = j :=
    congrArg (fun x : VitaliFiniteCenterPair B C => (x.1 : T)) he
  have hc' : vitaliFiniteCenter B C i = c :=
    congrArg (fun x : VitaliFiniteCenterPair B C => (x.2 : X)) he
  refine ⟨i, ?_, hc'⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

/-- Enumerating the center pairs preserves every radius-R candidate cover. -/
theorem vitaliFinite_indexed_cover {T X : Type*} [MetricSpace X]
    (B : Finset T) (C : T → Finset X) (Q : T → Set X) (R : ℝ)
    (hCover : ∀ j ∈ B, Q j ⊆ ⋃ c ∈ C j, Metric.ball c R) :
    ∀ j ∈ B,
      Q j ⊆ ⋃ i ∈ vitaliFiniteCandidates B C j,
        Metric.ball (vitaliFiniteCenter B C i) R := by
  classical
  intro j hj x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hCover j hj hx)
  obtain ⟨hcC, hxBall⟩ := Set.mem_iUnion.mp hc
  obtain ⟨i, hi, hci⟩ := vitaliFinite_index_exists B C j hj c hcC
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨hi, by simpa only [hci] using hxBall⟩⟩

/-- An indexed center belongs to the finite net of its parent tube. -/
theorem vitaliFinite_center_mem {T X : Type*}
    (B : Finset T) (C : T → Finset X)
    (i : Fin (Fintype.card (VitaliFiniteCenterPair B C))) :
    vitaliFiniteCenter B C i ∈ C (vitaliFiniteParent B C i) := by
  exact ((vitaliFiniteCenterEquiv B C) i).2.2

/-- Compactness of the closure of every actual greedy gain follows from
    boundedness of its dyadic level in a proper metric space. -/
theorem ConcreteTubeBallGeometry.gain_compact_closure_of_bounded_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) (j : T) :
    IsCompact (closure (g.gain m j)) := by
  exact (hBound.subset (g.gain_subset_dyadicLevel m j)).isCompact_closure

/-- The greedy stage correspondence follows when the selected tubes are
    precisely the first K distinct choices and their stages lie below K. -/
theorem ConcreteTubeBallGeometry.stages_of_selected_range
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hRange : g.B m =
      (Finset.range ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊).image
          (g.chosen m))
    (hStageBound : ∀ j ∈ g.B m,
      g.stage m j < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hInjective : ∀ k l,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      l < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      g.chosen m k = g.chosen m l → k = l) :
    ∀ k < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k := by
  intro k hk
  have hj : g.chosen m k ∈ g.B m := by
    rw [hRange]
    exact Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr hk, rfl⟩
  refine ⟨hj, ?_⟩
  exact hInjective (g.stage m (g.chosen m k)) k
    (hStageBound (g.chosen m k) hj) hk
    (g.hChosen m (g.chosen m k) hj)

/-- Instantiate the geometric Vitali theorem once the greedy level is
    bounded and the selected stages match their parent tube indices. -/
theorem ConcreteTubeBallGeometry.exists_greedy_vitali_of_bounded_level
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hStages : ∀ k < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k)
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) :
    ∃ S : T → Finset X,
      (∀ j ∈ g.B m, ∀ c ∈ S j, c ∈ g.gain m j) ∧
      (∀ j ∈ g.B m, ∀ c ∈ S j, ∀ c' ∈ S j, c ≠ c' →
        Disjoint (Metric.ball c R) (Metric.ball c' R)) ∧
      (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
        ⋃ j ∈ g.B m, ⋃ c ∈ S j,
          tubes j ∩ Metric.ball c (3 * R)) := by
  exact g.exists_greedy_vitali_from_compact_gains m R hR hStages
    (fun j _ => g.gain_compact_closure_of_bounded_level m hBound j)



/-- A finite occupied net for a greedy gain in a bounded dyadic level. -/
noncomputable def ConcreteTubeBallGeometry.finiteGainNet
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) (j : T) : Finset X :=
  Classical.choose (exists_finite_occupied_radius_cover
    (g.gain m j) R hR (g.gain_compact_closure_of_bounded_level m hBound j))

/-- Centers in the finite gain net belong to the corresponding greedy gain. -/
theorem ConcreteTubeBallGeometry.finiteGainNet_mem
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (j : T) (c : X) (hc : c ∈ g.finiteGainNet m R hR hBound j) :
    c ∈ g.gain m j := by
  exact (Classical.choose_spec (exists_finite_occupied_radius_cover
    (g.gain m j) R hR
    (g.gain_compact_closure_of_bounded_level m hBound j))).1 c hc

/-- The finite gain net covers its parent gain at radius R. -/
theorem ConcreteTubeBallGeometry.finiteGainNet_cover
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) (j : T) :
    g.gain m j ⊆ ⋃ c ∈ g.finiteGainNet m R hR hBound j,
      Metric.ball c R := by
  exact (Classical.choose_spec (exists_finite_occupied_radius_cover
    (g.gain m j) R hR
    (g.gain_compact_closure_of_bounded_level m hBound j))).2

/-- Finite occupied gain nets admit a single `Fin` indexing for all selected
    tube–center pairs at a fixed dyadic level. -/
theorem ConcreteTubeBallGeometry.finiteGainNet_indexed_cover
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (R : ℝ) (hR : 0 < R)
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) :
    let C : T → Finset X := g.finiteGainNet m R hR hBound
    ∀ j ∈ g.B m,
      g.gain m j ⊆ ⋃ i ∈ vitaliFiniteCandidates (g.B m) C j,
        Metric.ball (vitaliFiniteCenter (g.B m) C i) R := by
  exact vitaliFinite_indexed_cover (g.B m)
    (g.finiteGainNet m R hR hBound) (g.gain m) R
    (fun j _ => g.finiteGainNet_cover m R hR hBound j)

/-- Specialization of compact greedy-gain closures to finite-dimensional
    Euclidean space. -/
theorem ConcreteTubeBallGeometry.euclidean_gain_compact_closure
    {T : Type*} [Fintype T] (n : ℕ)
    (tubes : T → Set (EuclideanSpace ℝ (Fin n)))
    (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hBound : Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) (j : T) :
    IsCompact (closure (g.gain m j)) := by
  exact g.gain_compact_closure_of_bounded_level m hBound j



/-- Supply the indexed Vitali candidate data from occupied finite gain nets.
    The indexing condition records that the ball labels enumerate those nets. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofIndexedGainNets
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (centers : ∀ m, Fin (g.ballCount m) → X)
    (hBall : ∀ m i, g.ball m i = Metric.ball (centers m i) (radius m))
    (candidates : ∀ m, T → Finset (Fin (g.ballCount m)))
    (hIndexed : ∀ m j, j ∈ g.B m →
      ∀ c ∈ g.finiteGainNet m (radius m) (hRadius m) (hBound m) j,
        ∃ i ∈ candidates m j, centers m i = c)
    (hRange : ∀ m, g.B m =
      (Finset.range ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊).image
          (g.chosen m))
    (hStageBound : ∀ m j, j ∈ g.B m →
      g.stage m j < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hInjective : ∀ m k l,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      l < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      g.chosen m k = g.chosen m l → k = l) :
    ConcreteGreedyVitaliCandidates tubes g := by
  classical
  refine {
    radius := radius
    hRadius := hRadius
    centers := centers
    hBall := hBall
    candidates := candidates
    hStages := fun m k hk =>
      g.stages_of_selected_range m (hRange m)
        (hStageBound m) (hInjective m) k hk
    hLocal := ?_ }
  intro m j hj x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
    (g.finiteGainNet_cover m (radius m) (hRadius m) (hBound m) j hx)
  obtain ⟨hcNet, hxBall⟩ := Set.mem_iUnion.mp hc
  obtain ⟨i, hi, hCenter⟩ := hIndexed m j hj c hcNet
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
  rw [hBall m i, hCenter]
  exact hxBall



/-! ## Compatibility with the existing indexed geometry -/

/-- Identify the finite gain-net centers with balls already indexed by the
original geometry. Extra ball indices are allowed, and the original geometry
and its retained labels are unchanged. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofExistingGainNetIndexMap
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] {tubes : T → Set X}
    (g : ConcreteTubeBallGeometry tubes)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (centers : ∀ m, Fin (g.ballCount m) → X)
    (hBall : ∀ m i, g.ball m i = Metric.ball (centers m i) (radius m))
    (index : ∀ m, VitaliFiniteCenterPair (g.B m)
      (g.finiteGainNet m (radius m) (hRadius m) (hBound m)) →
        Fin (g.ballCount m))
    (hIndexCenter : ∀ m p, centers m (index m p) = p.2.1)
    (hRange : ∀ m, g.B m =
      (Finset.range ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊).image
          (g.chosen m))
    (hStageBound : ∀ m j, j ∈ g.B m →
      g.stage m j < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hInjective : ∀ m k l,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      l < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      g.chosen m k = g.chosen m l → k = l) :
    ConcreteGreedyVitaliCandidates tubes g := by
  classical
  let candidates : ∀ m, T → Finset (Fin (g.ballCount m)) :=
    fun m j => (Finset.univ : Finset (Fin (g.ballCount m))).filter
      (fun i => ∃ p : VitaliFiniteCenterPair (g.B m)
        (g.finiteGainNet m (radius m) (hRadius m) (hBound m)),
        p.1.1 = j ∧ index m p = i)
  apply ConcreteGreedyVitaliCandidates.ofIndexedGainNets g
    radius hRadius hBound centers hBall candidates
  · intro m j hj c hc
    let p : VitaliFiniteCenterPair (g.B m)
        (g.finiteGainNet m (radius m) (hRadius m) (hBound m)) :=
      ⟨⟨j, hj⟩, ⟨c, hc⟩⟩
    refine ⟨index m p, ?_, hIndexCenter m p⟩
    change index m p ∈ candidates m j
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨p, rfl, rfl⟩⟩
  · exact hRange
  · exact hStageBound
  · exact hInjective


/-! ## Constructing the original indexed ball family -/

/-- The finite nets determine the ball indices before the retained Vitali
pieces are formed. Every initial selected tube has a net center. -/
noncomputable def ConcreteTubeBallGeometry.ofGreedyNetFamily
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (hC : ∀ m j, j ∈ B m → (C m j).Nonempty)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ) :
    ConcreteTubeBallGeometry tubes := by
  classical
  exact {
    B := B
    P := fun _ => ∅
    ballCount := fun m => Fintype.card (VitaliFiniteCenterPair (B m) (C m))
    ball := fun m i =>
      Metric.ball (vitaliFiniteCenter (B m) (C m) i) (radius m)
    chosen := chosen
    stage := stage
    hChosen := hChosen
    hPSelected := by
      intro m p hp
      simp at hp
    hPBall := by
      intro m p hp
      simp at hp
    selectedBall := fun m j =>
      (vitaliFiniteCenterEquiv (B m) (C m)).symm
        ⟨j, ⟨Classical.choose (hC m j.val j.property),
          Classical.choose_spec (hC m j.val j.property)⟩⟩
    trim := fun _ _ _ => Set.univ
  }

/-- The original ball function is exactly the indexed finite-net ball. -/
theorem ConcreteTubeBallGeometry.ofGreedyNetFamily_ball
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (hC : ∀ m j, j ∈ B m → (C m j).Nonempty)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin (Fintype.card (VitaliFiniteCenterPair (B m) (C m)))) :
    (ConcreteTubeBallGeometry.ofGreedyNetFamily tubes B chosen stage hChosen
      C hC radius).ball m i =
      Metric.ball (vitaliFiniteCenter (B m) (C m) i) (radius m) := by
  rfl

/-- The indexed centers give the local cover used by the occupied Vitali
selection, with the geometry's original balls and indices. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofGreedyNetFamily
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (hC : ∀ m j, j ∈ B m → (C m j).Nonempty)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hStages : ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      chosen m k ∈ B m ∧ stage m (chosen m k) = k)
    (hCover : ∀ m j, j ∈ B m →
      Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j) ⊆
          ⋃ c ∈ C m j, Metric.ball c (radius m)) :
    ConcreteGreedyVitaliCandidates tubes
      (ConcreteTubeBallGeometry.ofGreedyNetFamily tubes B chosen stage
        hChosen C hC radius) := by
  classical
  let g := ConcreteTubeBallGeometry.ofGreedyNetFamily tubes B chosen
    stage hChosen C hC radius
  refine {
    radius := radius
    hRadius := hRadius
    centers := fun m i => vitaliFiniteCenter (B m) (C m) i
    hBall := ?_
    candidates := fun m j => vitaliFiniteCandidates (B m) (C m) j
    hStages := ?_
    hLocal := ?_
  }
  · intro m i
    rfl
  · intro m k hk
    change chosen m k ∈ B m ∧ stage m (chosen m k) = k
    exact hStages m k hk
  · intro m j hj x hx
    have hjB : j ∈ B m := hj
    have hxGain : x ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j) := by
      change x ∈ (if j ∈ B m then
        Kakeya.Eighty4.concreteGreedyGain tubes
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (chosen m) (stage m j) else ∅) at hx
      simpa only [if_pos hjB] using hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hCover m j hjB hxGain)
    obtain ⟨hcNet, hxc⟩ := Set.mem_iUnion.mp hc
    obtain ⟨i, hi, hci⟩ := vitaliFinite_index_exists
      (B m) (C m) j hjB c hcNet
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
    change x ∈ Metric.ball (vitaliFiniteCenter (B m) (C m) i) (radius m)
    simpa only [hci] using hxc


/-- Every ball indexed from centers in the parent greedy gains meets the
corresponding dyadic level. -/
theorem ConcreteTubeBallGeometry.ofGreedyNetFamily_ball_occupied
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (hC : ∀ m j, j ∈ B m → (C m j).Nonempty)
    (hCenters : ∀ m j, j ∈ B m → ∀ c ∈ C m j,
      c ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : Fin (Fintype.card (VitaliFiniteCenterPair (B m) (C m)))) :
    ((ConcreteTubeBallGeometry.ofGreedyNetFamily tubes B chosen stage
        hChosen C hC radius).ball m i ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty := by
  let p : VitaliFiniteCenterPair (B m) (C m) :=
    vitaliFiniteCenterEquiv (B m) (C m) i
  have hc : p.2.1 ∈ C m p.1.1 := p.2.2
  have hxGain := hCenters m p.1.1 p.1.2 p.2.1 hc
  have hxBand : p.2.1 ∈
      Kakeya.Eighty4.concreteDyadicBand tubes m :=
    Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m p.1.1) hxGain
  refine ⟨p.2.1, ?_, hxBand⟩
  change p.2.1 ∈ Metric.ball (vitaliFiniteCenter (B m) (C m) i) (radius m)
  have hcenter : vitaliFiniteCenter (B m) (C m) i = p.2.1 := rfl
  rw [hcenter]
  exact Metric.mem_ball_self (hRadius m)

/-- A finite radius-R center net for each actual greedy gain in a bounded
level. -/
noncomputable def greedyFiniteNet
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] (tubes : T → Set X)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) : Finset X := by
  have hCompact : IsCompact (closure
      (Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))) :=
    ((hBound m).subset
      (Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))).isCompact_closure
  exact Classical.choose (exists_finite_occupied_radius_cover
    (Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j)) (radius m) (hRadius m) hCompact)

/-- The net centers are points of the original greedy gain. -/
theorem greedyFiniteNet_mem
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] (tubes : T → Set X)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T)
    (c : X)
    (hc : c ∈ greedyFiniteNet tubes chosen stage radius hRadius hBound m j) :
    c ∈ Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j) := by
  unfold greedyFiniteNet at hc
  exact (Classical.choose_spec (exists_finite_occupied_radius_cover
    (Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j)) (radius m) (hRadius m)
    ((hBound m).subset
      (Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))).isCompact_closure)).1 c hc

/-- Each original greedy gain is covered by its radius-R finite net. -/
theorem greedyFiniteNet_cover
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] (tubes : T → Set X)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) :
    Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j) ⊆
        ⋃ c ∈ greedyFiniteNet tubes chosen stage radius hRadius hBound m j,
          Metric.ball c (radius m) := by
  exact (Classical.choose_spec (exists_finite_occupied_radius_cover
    (Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j)) (radius m) (hRadius m)
    ((hBound m).subset
      (Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j))).isCompact_closure)).2

/-- Empty greedy gains have no finite-net centers. -/
theorem greedyFiniteNet_empty_of_gain_empty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] (tubes : T → Set X)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T)
    (hEmpty : Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j) = ∅) :
    greedyFiniteNet tubes chosen stage radius hRadius hBound m j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hx := greedyFiniteNet_mem tubes chosen stage radius
    hRadius hBound m j c hc
  rw [hEmpty] at hx
  exact hx

/-- A nonempty greedy gain has a center in its finite net. -/
theorem greedyFiniteNet_nonempty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Fintype T] (tubes : T → Set X)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T)
    (hGain : (Kakeya.Eighty4.concreteGreedyGain tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (chosen m) (stage m j)).Nonempty) :
    (greedyFiniteNet tubes chosen stage radius hRadius hBound m j).Nonempty := by
  obtain ⟨x, hx⟩ := hGain
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
    (greedyFiniteNet_cover tubes chosen stage radius hRadius hBound m j hx)
  obtain ⟨hcNet, _⟩ := Set.mem_iUnion.mp hc
  exact ⟨c, hcNet⟩

/-! ## Finite ball indexing with empty greedy gains -/

/-- A finite center index with one additional fallback index. -/
noncomputable def vitaliPaddedCenterEquiv {T X : Type*}
    (B : Finset T) (C : T → Finset X) :
    Fin (Fintype.card (Option (VitaliFiniteCenterPair B C))) ≃
      Option (VitaliFiniteCenterPair B C) := by
  classical
  exact (Fintype.equivFin (Option (VitaliFiniteCenterPair B C))).symm

/-- The additional index has an arbitrary center; genuine indices retain
    their original finite-net centers. -/
noncomputable def vitaliPaddedCenter {T X : Type*} [Nonempty X]
    (B : Finset T) (C : T → Finset X)
    (i : Fin (Fintype.card (Option (VitaliFiniteCenterPair B C)))) : X :=
  match vitaliPaddedCenterEquiv B C i with
  | some p => p.2.1
  | none => Classical.choice (inferInstance : Nonempty X)

/-- Only genuine tube–center pairs are Vitali candidates. -/
noncomputable def vitaliPaddedCandidates {T X : Type*}
    (B : Finset T) (C : T → Finset X) (j : T) :
    Finset (Fin (Fintype.card (Option (VitaliFiniteCenterPair B C)))) := by
  classical
  exact Finset.univ.filter (fun i =>
    ∃ p : VitaliFiniteCenterPair B C,
      vitaliPaddedCenterEquiv B C i = some p ∧ p.1.1 = j)

/-- The additional structural ball is never a Vitali candidate. -/
theorem vitaliPadded_fallback_not_candidate {T X : Type*}
    (B : Finset T) (C : T → Finset X) (j : T) :
    (vitaliPaddedCenterEquiv B C).symm none ∉
      vitaliPaddedCandidates B C j := by
  classical
  intro h
  have hp : ∃ p : VitaliFiniteCenterPair B C,
      vitaliPaddedCenterEquiv B C
          ((vitaliPaddedCenterEquiv B C).symm none) = some p ∧ p.1.1 = j := by
    unfold vitaliPaddedCandidates at h
    exact (Finset.mem_filter.mp h).2
  obtain ⟨p, hp, _⟩ := hp
  have hnone : vitaliPaddedCenterEquiv B C
      ((vitaliPaddedCenterEquiv B C).symm none) = none :=
    (vitaliPaddedCenterEquiv B C).apply_symm_apply none
  rw [hnone] at hp
  cases hp

/-- Each gain-net center has a genuine padded index in its own tube fiber. -/
theorem vitaliPadded_index_exists {T X : Type*} [Nonempty X]
    (B : Finset T) (C : T → Finset X)
    (j : T) (hj : j ∈ B) (c : X) (hc : c ∈ C j) :
    ∃ i : Fin (Fintype.card (Option (VitaliFiniteCenterPair B C))),
      i ∈ vitaliPaddedCandidates B C j ∧
        vitaliPaddedCenter B C i = c := by
  classical
  let p : VitaliFiniteCenterPair B C := ⟨⟨j, hj⟩, ⟨c, hc⟩⟩
  let i := (vitaliPaddedCenterEquiv B C).symm (some p)
  have he : vitaliPaddedCenterEquiv B C i = some p :=
    (vitaliPaddedCenterEquiv B C).apply_symm_apply (some p)
  have hi : i ∈ vitaliPaddedCandidates B C j := by
    unfold vitaliPaddedCandidates
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, he, rfl⟩⟩
  refine ⟨i, hi, ?_⟩
  unfold vitaliPaddedCenter
  rw [he]

/-- Finite gain-net covering survives the padded ball indexing. -/
theorem vitaliPadded_indexed_cover {T X : Type*}
    [MetricSpace X] [Nonempty X]
    (B : Finset T) (C : T → Finset X) (Q : T → Set X) (R : ℝ)
    (hCover : ∀ j ∈ B, Q j ⊆ ⋃ c ∈ C j, Metric.ball c R) :
    ∀ j ∈ B, Q j ⊆ ⋃ i ∈ vitaliPaddedCandidates B C j,
      Metric.ball (vitaliPaddedCenter B C i) R := by
  classical
  intro j hj x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hCover j hj hx)
  obtain ⟨hcC, hxc⟩ := Set.mem_iUnion.mp hc
  obtain ⟨i, hi, hci⟩ := vitaliPadded_index_exists B C j hj c hcC
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨hi, by simpa only [hci] using hxc⟩⟩

/-- The original greedy-choice and stage data with all gain-net centers
    indexed, even when some selected gains are empty. -/
noncomputable def ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T), T → Finset X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ) :
    ConcreteTubeBallGeometry tubes := by
  classical
  exact {
    B := B
    P := fun _ => ∅
    ballCount := fun m =>
      Fintype.card (Option (VitaliFiniteCenterPair (B m) (C m)))
    ball := fun m i =>
      Metric.ball (vitaliPaddedCenter (B m) (C m) i) (radius m)
    chosen := chosen
    stage := stage
    hChosen := hChosen
    hPSelected := by
      intro m p hp
      simp at hp
    hPBall := by
      intro m p hp
      simp at hp
    selectedBall := fun m j =>
      (vitaliPaddedCenterEquiv (B m) (C m)).symm
        (if h : (C m j.val).Nonempty then
          some ⟨j, ⟨Classical.choose h, Classical.choose_spec h⟩⟩
        else none)
    trim := fun _ _ _ => Set.univ
  }

/-- The padded geometry uses precisely the genuine finite-net centers
    as candidates for the occupied Vitali selection. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofGreedyNetFamilyAllowEmpty
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T]
    (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (C : ∀ m, T → Finset X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hStages : ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      chosen m k ∈ B m ∧ stage m (chosen m k) = k)
    (hCover : ∀ m j, j ∈ B m →
      Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j) ⊆
          ⋃ c ∈ C m j, Metric.ball c (radius m)) :
    ConcreteGreedyVitaliCandidates tubes
      (ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B chosen
        stage hChosen C radius) := by
  classical
  let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B
    chosen stage hChosen C radius
  refine {
    radius := radius
    hRadius := hRadius
    centers := fun m i => vitaliPaddedCenter (B m) (C m) i
    hBall := ?_
    candidates := fun m j => vitaliPaddedCandidates (B m) (C m) j
    hStages := ?_
    hLocal := ?_
  }
  · intro m i
    rfl
  · intro m k hk
    change chosen m k ∈ B m ∧ stage m (chosen m k) = k
    exact hStages m k hk
  · intro m j hj x hx
    have hxGain : x ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (chosen m) (stage m j) := by
      change x ∈ (if j ∈ B m then
        Kakeya.Eighty4.concreteGreedyGain tubes
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (chosen m) (stage m j) else ∅) at hx
      change j ∈ B m at hj
      simpa only [if_pos hj] using hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hCover m j hj hxGain)
    obtain ⟨hcNet, hxc⟩ := Set.mem_iUnion.mp hc
    obtain ⟨i, hi, hci⟩ := vitaliPadded_index_exists
      (B m) (C m) j hj c hcNet
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ?_⟩⟩
    change x ∈ Metric.ball (vitaliPaddedCenter (B m) (C m) i) (radius m)
    simpa only [hci] using hxc

/-- Construct the original indexed ball family from bounded greedy gains.
    Empty gains have empty center nets and no occupied candidate labels. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Nonempty X] [Fintype T] (tubes : T → Set X)
    (B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T)
    (chosen : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → T)
    (stage : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → ℕ)
    (hChosen : ∀ m j, j ∈ B m → chosen m (stage m j) = j)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m))
    (hStages : ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      chosen m k ∈ B m ∧ stage m (chosen m k) = k) :
    let C := greedyFiniteNet tubes chosen stage radius hRadius hBound
    ConcreteGreedyVitaliCandidates tubes
      (ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B chosen
        stage hChosen C radius) := by
  exact ConcreteGreedyVitaliCandidates.ofGreedyNetFamilyAllowEmpty
    tubes B chosen stage hChosen
    (greedyFiniteNet tubes chosen stage radius hRadius hBound)
    radius hRadius hStages
    (fun m j _ => greedyFiniteNet_cover tubes chosen stage radius
      hRadius hBound m j)

/-! ## Greedy selection without replacement -/

/-- Choose a maximal residual-mass tube among those not yet used. -/
noncomputable def maximalUnusedChoice
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (used : Finset T) : T := by
  classical
  let residual := F \ (⋃ j ∈ used, tubes j)
  if h : (Finset.univ \ used).Nonempty then
    exact Classical.choose
      (exists_maximal_unused_tube μ tubes residual used h)
  else
    exact Classical.choice inferInstance

/-- The choice belongs to the unused set and maximizes residual mass there. -/
theorem maximalUnusedChoice_spec
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (used : Finset T) (h : (Finset.univ \ used).Nonempty) :
    maximalUnusedChoice μ tubes F used ∈ Finset.univ \ used ∧
    ∀ j ∈ Finset.univ \ used,
      Kakeya.Conditional.mass μ
          ((F \ (⋃ r ∈ used, tubes r)) ∩ tubes j) ≤
        Kakeya.Conditional.mass μ
          ((F \ (⋃ r ∈ used, tubes r)) ∩
            tubes (maximalUnusedChoice μ tubes F used)) := by
  classical
  simpa only [maximalUnusedChoice, dif_pos h] using
    (Classical.choose_spec
      (exists_maximal_unused_tube μ tubes
        (F \ (⋃ r ∈ used, tubes r)) used h))

/-- The indices used before step `k`. -/
noncomputable def maximalUnusedUsed
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X) :
    ℕ → Finset T :=
  Nat.rec ∅ (fun _ used =>
    insert (maximalUnusedChoice μ tubes F used) used)

/-- Recursively selected original tube index. -/
noncomputable def maximalUnusedChosen
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) : T :=
  maximalUnusedChoice μ tubes F (maximalUnusedUsed μ tubes F k)

/-- Used indices are exactly the first `k` choices. -/
theorem maximalUnusedUsed_eq_image
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) :
    maximalUnusedUsed μ tubes F k =
      (Finset.range k).image (maximalUnusedChosen μ tubes F) := by
  classical
  induction k with
  | zero => simp [maximalUnusedUsed]
  | succ k ih =>
      change insert (maximalUnusedChosen μ tubes F k)
          (maximalUnusedUsed μ tubes F k) =
        (Finset.range (k + 1)).image (maximalUnusedChosen μ tubes F)
      ext j
      constructor
      · intro hj
        rcases Finset.mem_insert.mp hj with h | h
        · exact Finset.mem_image.mpr
            ⟨k, Finset.mem_range.mpr (by omega), h.symm⟩
        · obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp (ih ▸ h)
          exact Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr
              (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)), hEq⟩
      · intro hj
        obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hj
        have hik : i ≤ k := by
          have := Finset.mem_range.mp hi
          omega
        rcases lt_or_eq_of_le hik with hlt | heq
        · apply Finset.mem_insert_of_mem
          rw [ih]
          exact Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr hlt, hEq⟩
        · exact Finset.mem_insert.mpr
            (Or.inl (by simpa only [heq] using hEq.symm))

/-- An unused index is available at every step below the tube count. -/
theorem maximalUnused_available
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) (hk : k < Fintype.card T) :
    (Finset.univ \ maximalUnusedUsed μ tubes F k).Nonempty := by
  classical
  have hCard : (maximalUnusedUsed μ tubes F k).card ≤ k := by
    rw [maximalUnusedUsed_eq_image]
    calc
      ((Finset.range k).image (maximalUnusedChosen μ tubes F)).card ≤
          (Finset.range k).card := Finset.card_image_le
      _ = k := by simp
  by_contra hEmpty
  have hSub : (Finset.univ : Finset T) ⊆
      maximalUnusedUsed μ tubes F k := by
    intro j _
    by_contra hj
    exact hEmpty ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hFull := Finset.card_le_card hSub
  simp only [Finset.card_univ] at hFull
  omega

/-- Every choice before the tube count is new. -/
theorem maximalUnusedChosen_not_mem
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) (hk : k < Fintype.card T) :
    maximalUnusedChosen μ tubes F k ∉ maximalUnusedUsed μ tubes F k := by
  have h := (maximalUnusedChoice_spec μ tubes F
    (maximalUnusedUsed μ tubes F k)
    (maximalUnused_available μ tubes F k hk)).1
  exact (Finset.mem_sdiff.mp h).2

/-- The first `N` selected tube indices are distinct. -/
theorem maximalUnusedChosen_injective_initial
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    {i j : ℕ} (hi : i < Fintype.card T) (hj : j < Fintype.card T)
    (heq : maximalUnusedChosen μ tubes F i =
      maximalUnusedChosen μ tubes F j) : i = j := by
  classical
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hMem : maximalUnusedChosen μ tubes F i ∈
        maximalUnusedUsed μ tubes F j := by
      rw [maximalUnusedUsed_eq_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩
    have hNot := maximalUnusedChosen_not_mem μ tubes F j hj
    exact hNot (heq ▸ hMem)
  · have hMem : maximalUnusedChosen μ tubes F j ∈
        maximalUnusedUsed μ tubes F i := by
      rw [maximalUnusedUsed_eq_image]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hji, rfl⟩
    have hNot := maximalUnusedChosen_not_mem μ tubes F i hi
    exact hNot (heq.symm ▸ hMem)

/-- The unions indexed by used tubes and by earlier greedy stages coincide. -/
theorem maximalUnusedUsed_union_eq_prefix
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) :
    (⋃ j ∈ maximalUnusedUsed μ tubes F k, tubes j) =
      prefixTubeUnion tubes (maximalUnusedChosen μ tubes F) k := by
  classical
  rw [maximalUnusedUsed_eq_image]
  ext x
  simp only [prefixTubeUnion, Set.mem_iUnion,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨maximalUnusedChosen μ tubes F i, ⟨i, hi, rfl⟩, hx⟩

/-- The recursive choice maximizes residual mass among all unused tubes. -/
theorem maximalUnusedChosen_maximal
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) (F : Set X)
    (k : ℕ) (j : T)
    (hj : j ∉ (Finset.range k).image (maximalUnusedChosen μ tubes F)) :
    Kakeya.Conditional.mass μ
        ((F \ prefixTubeUnion tubes
          (maximalUnusedChosen μ tubes F) k) ∩ tubes j) ≤
      Kakeya.Conditional.mass μ
        ((F \ prefixTubeUnion tubes
          (maximalUnusedChosen μ tubes F) k) ∩
          tubes (maximalUnusedChosen μ tubes F k)) := by
  classical
  let used := maximalUnusedUsed μ tubes F k
  have hjUnused : j ∈ Finset.univ \ used := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      by simpa only [used, maximalUnusedUsed_eq_image] using hj⟩
  have hNonempty : (Finset.univ \ used).Nonempty := ⟨j, hjUnused⟩
  have hmax := (maximalUnusedChoice_spec μ tubes F used hNonempty).2 j hjUnused
  change Kakeya.Conditional.mass μ
      ((F \ prefixTubeUnion tubes
        (maximalUnusedChosen μ tubes F) k) ∩ tubes j) ≤
    Kakeya.Conditional.mass μ
      ((F \ prefixTubeUnion tubes
        (maximalUnusedChosen μ tubes F) k) ∩
        tubes (maximalUnusedChosen μ tubes F k))
  rw [← maximalUnusedUsed_union_eq_prefix μ tubes F k]
  exact hmax

/-- Step budget `ceil(N / 2^m)` does not exceed the number of original tubes. -/
theorem maximalUnused_dyadic_step_le_card
    (N : ℕ) (m : Kakeya.Eighty4.DyadicIndex N) :
    ⌈(N : ℝ) / Kakeya.Eighty4.dyadicScale N m⌉₊ ≤ N := by
  apply (Nat.ceil_le).2
  have hq : (1 : ℝ) ≤ Kakeya.Eighty4.dyadicScale N m := by
    change (1 : ℝ) ≤ (2 : ℝ) ^ m.val
    exact one_le_pow₀ (by norm_num)
  have hqPos : 0 < Kakeya.Eighty4.dyadicScale N m := lt_of_lt_of_le (by norm_num) hq
  apply (div_le_iff₀ hqPos).2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hq)]

/-- The selected set consists of the first `ceil(N / 2^m)` greedy choices. -/
noncomputable def maximalUnusedDyadicChosen
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : ℕ → T :=
  maximalUnusedChosen μ tubes (Kakeya.Eighty4.concreteDyadicBand tubes m)

noncomputable def maximalUnusedDyadicSelected
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : Finset T := by
  classical
  exact (Finset.range ⌈(Fintype.card T : ℝ) /
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊).image
      (maximalUnusedDyadicChosen μ tubes m)

/-- The first stage at which a selected tube appears. -/
noncomputable def maximalUnusedDyadicStage
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) : ℕ :=
  if h : ∃ k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
        maximalUnusedDyadicChosen μ tubes m k = j then
    Classical.choose h
  else 0

/-- The stage is the inverse of the choice sequence on its selected range. -/
theorem maximalUnusedDyadicStage_chosen
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (i : ℕ)
    (hi : i < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊) :
    maximalUnusedDyadicStage μ tubes m (maximalUnusedDyadicChosen μ tubes m i) = i := by
  classical
  have he : ∃ k < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊,
      maximalUnusedDyadicChosen μ tubes m k =
        maximalUnusedDyadicChosen μ tubes m i := ⟨i, hi, rfl⟩
  have hk := (Classical.choose_spec he).1
  have hval := (Classical.choose_spec he).2
  unfold maximalUnusedDyadicStage
  rw [dif_pos he]
  exact maximalUnusedChosen_injective_initial μ tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m)
    (lt_of_lt_of_le hk (maximalUnused_dyadic_step_le_card _ m))
    (lt_of_lt_of_le hi (maximalUnused_dyadic_step_le_card _ m)) hval

/-- Selected tube labels have the correct recorded stages. -/
theorem maximalUnusedDyadic_hChosen
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) :
    ∀ m j, j ∈ maximalUnusedDyadicSelected μ tubes m →
      maximalUnusedDyadicChosen μ tubes m
        (maximalUnusedDyadicStage μ tubes m j) = j := by
  classical
  intro m j hj
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hj
  have hi' := Finset.mem_range.mp hi
  calc
    maximalUnusedDyadicChosen μ tubes m (maximalUnusedDyadicStage μ tubes m j) =
        maximalUnusedDyadicChosen μ tubes m
          (maximalUnusedDyadicStage μ tubes m
            (maximalUnusedDyadicChosen μ tubes m i)) := by rw [heq]
    _ = maximalUnusedDyadicChosen μ tubes m i := by
          rw [maximalUnusedDyadicStage_chosen μ tubes m i hi']
    _ = j := heq

/-- The same construction proves selection membership and stage inversion. -/
theorem maximalUnusedDyadic_hStages
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) :
    ∀ m k,
      k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      maximalUnusedDyadicChosen μ tubes m k ∈
        maximalUnusedDyadicSelected μ tubes m ∧
      maximalUnusedDyadicStage μ tubes m
        (maximalUnusedDyadicChosen μ tubes m k) = k := by
  classical
  intro m k hk
  constructor
  · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  · exact maximalUnusedDyadicStage_chosen μ tubes m k hk


/-- The first dyadic greedy choices are distinct, so selected-tube
cardinality equals the greedy step count. -/
theorem maximalUnusedDyadicSelected_card
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (maximalUnusedDyadicSelected μ tubes m).card =
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
  classical
  have hinj : Set.InjOn (maximalUnusedDyadicChosen μ tubes m)
      (↑(Finset.range ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊) : Set ℕ) := by
    intro i hi j hj heq
    exact maximalUnusedChosen_injective_initial μ tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (lt_of_lt_of_le (Finset.mem_range.mp hi)
        (maximalUnused_dyadic_step_le_card _ m))
      (lt_of_lt_of_le (Finset.mem_range.mp hj)
        (maximalUnused_dyadic_step_le_card _ m)) heq
  have hc := Finset.card_image_of_injOn hinj
  simpa only [maximalUnusedDyadicSelected, Finset.card_range] using hc

/-- The resulting indexed choice satisfies the same maximal-unused condition
as the concrete tube–ball geometry. -/
theorem maximalUnusedDyadic_hMax
    {X T : Type*} [MeasurableSpace X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X) :
    ∀ m k j, j ∉ (Finset.range k).image (maximalUnusedDyadicChosen μ tubes m) →
      Kakeya.Conditional.mass μ
        ((Kakeya.Eighty4.concreteDyadicBand tubes m \
          prefixTubeUnion tubes
            (maximalUnusedDyadicChosen μ tubes m) k) ∩ tubes j) ≤
      Kakeya.Conditional.mass μ
        ((Kakeya.Eighty4.concreteDyadicBand tubes m \
          prefixTubeUnion tubes
            (maximalUnusedDyadicChosen μ tubes m) k) ∩
            tubes (maximalUnusedDyadicChosen μ tubes m k)) := by
  intro m k j hj
  exact maximalUnusedChosen_maximal μ tubes
    (Kakeya.Eighty4.concreteDyadicBand tubes m) k j hj


/-- The padded indexed geometry built from the nonrepeating greedy
    selector satisfies the unused-tube maximality condition. -/
theorem ConcreteTubeBallGeometry.ofGreedyNetFamily_maximalUnused
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (C : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T), T → Finset X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ) :
    (ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
      (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes)
      C radius).MaximalUnused μ := by
  intro m k j hj
  exact maximalUnusedDyadic_hMax μ tubes m k j hj

/-- The same generated geometry has the selected-stage correspondence. -/
theorem ConcreteTubeBallGeometry.ofGreedyNetFamily_hStages
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (C : ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T), T → Finset X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ) :
    let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes
      (maximalUnusedDyadicSelected μ tubes)
      (maximalUnusedDyadicChosen μ tubes)
      (maximalUnusedDyadicStage μ tubes)
      (maximalUnusedDyadic_hChosen μ tubes)
      C radius
    ∀ m k, k < ⌈(Fintype.card T : ℝ) /
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
      g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k := by
  exact maximalUnusedDyadic_hStages μ tubes

/-- Construct finite-net Vitali data from the maximal-unused greedy selector,
    including stages whose gains are empty. -/
noncomputable def ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) :
    let chosen := maximalUnusedDyadicChosen μ tubes
    let stage := maximalUnusedDyadicStage μ tubes
    let B := maximalUnusedDyadicSelected μ tubes
    let C := greedyFiniteNet tubes chosen stage radius hRadius hBound
    ConcreteGreedyVitaliCandidates tubes
      (ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B chosen
        stage (maximalUnusedDyadic_hChosen μ tubes) C radius) := by
  exact ConcreteGreedyVitaliCandidates.ofCompactGreedyGains
    tubes (maximalUnusedDyadicSelected μ tubes)
    (maximalUnusedDyadicChosen μ tubes)
    (maximalUnusedDyadicStage μ tubes)
    (maximalUnusedDyadic_hChosen μ tubes) radius hRadius hBound
    (maximalUnusedDyadic_hStages μ tubes)

/-- The finite-net geometry satisfies both greedy maximality and stage
    correspondence for the same tube selection used by its retained pieces. -/
theorem ConcreteGreedyVitaliCandidates.ofCompactMaximalUnusedGains_selection
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [ProperSpace X]
    [Nonempty X] [Fintype T] [Nonempty T]
    (μ : Measure X) (tubes : T → Set X)
    (radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ)
    (hRadius : ∀ m, 0 < radius m)
    (hBound : ∀ m, Bornology.IsBounded
      (Kakeya.Eighty4.concreteDyadicBand tubes m)) :
    let chosen := maximalUnusedDyadicChosen μ tubes
    let stage := maximalUnusedDyadicStage μ tubes
    let B := maximalUnusedDyadicSelected μ tubes
    let C := greedyFiniteNet tubes chosen stage radius hRadius hBound
    let g := ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty tubes B chosen
      stage (maximalUnusedDyadic_hChosen μ tubes) C radius
    g.MaximalUnused μ ∧
      (∀ m k, k < ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ →
        g.chosen m k ∈ g.B m ∧ g.stage m (g.chosen m k) = k) := by
  constructor
  · exact ConcreteTubeBallGeometry.ofGreedyNetFamily_maximalUnused
      μ tubes _ radius
  · exact ConcreteTubeBallGeometry.ofGreedyNetFamily_hStages
      μ tubes _ radius

/-! ## Canonical greedy recurrence and Euclidean triple-radius cost -/

/-- The greedy recurrence for the actual maximizing tube sequence, expressed
through the occupied retained family. -/
theorem ConcreteGreedyVitaliCandidates.retained_canonical_greedy_recurrence
    {X T : Type*} [MeasurableSpace X] [MetricSpace X]
    [Fintype T] [Nonempty T]
    (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (hN : 0 < Fintype.card T)
    (hT : ∀ j, MeasurableSet (tubes j))
    (hCanonical : ∀ m, g.chosen m =
      maximalUnusedDyadicChosen μ tubes m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (i : ℕ) :
    Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (d.retained.greedyQ m) (i + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (d.retained.greedyQ m) i := by
  have hMax : g.MaximalUnused μ := by
    intro m' k j hj
    have hj' : j ∉ (Finset.range k).image (maximalUnusedDyadicChosen μ tubes m') := by
      simpa only [hCanonical m'] using hj
    have h := maximalUnusedDyadic_hMax μ tubes m' k j hj'
    simpa only [hCanonical m'] using h
  have hNReal : 0 < (Fintype.card T : ℝ) := by exact_mod_cast hN
  exact d.retained_greedy_recurrence_of_maximal_unused μ tubes g
    hNReal hT hMax m i


/-- Build the analytic endpoint for the actual maximizing greedy sequence.
The triple-radius cost comes from the Euclidean volume estimate. -/
noncomputable def ConcreteTwoRadiusGreedy.ofCanonicalVitaliEuclidean
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (hN : 0 < Fintype.card T)
    (hCanonical : ∀ m, g.chosen m =
      maximalUnusedDyadicChosen μ
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hDeltaPow : b.deltaPow = δ ^ (k + 1))
    (hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C) :
    ConcreteTwoRadiusGreedy μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ)
      (k + 2) d.retained b := by
  exact ConcreteTwoRadiusGreedy.ofGreedyVitaliCandidates μ
    (fun j => Kakeya.unitTube (center j) (direction j) δ)
    (k + 2) g d b hRadius hT
    (fun m i => by
      have h := d.retained_canonical_greedy_recurrence
        μ (fun j => Kakeya.unitTube (center j) (direction j) δ)
          g hN hT hCanonical m i
      rw [d.retained_greedyQ_eq m] at h
      exact h)
    (fun m j i _ _ =>
      d.euclidean_triple_cost μ center direction δ hδ g b hT hv hDom
        hRadius hDeltaPow hCgeom m j i)

/-- The canonical greedy endpoint feeds the existing Theorem 4.6 data of
exactly the same occupied retained family. -/
theorem full_conditional_kakeya_of_canonicalVitaliEuclidean
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun j => Kakeya.unitTube (center j) (direction j) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun j => Kakeya.unitTube (center j) (direction j) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2) d.retained)
    (a : Paper46LargeLevelInputs μ
      (fun j => Kakeya.unitTube (center j) (direction j) δ) (k + 2)
      (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData)
    (hN : 0 < Fintype.card T)
    (hCanonical : ∀ m, g.chosen m =
      maximalUnusedDyadicChosen μ
        (fun j => Kakeya.unitTube (center j) (direction j) δ) m)
    (hT : ∀ j, MeasurableSet
      (Kakeya.unitTube (center j) (direction j) δ))
    (hv : ∀ j, direction j ≠ 0)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (hRadius : ∀ m, d.radius m = twoRadiusRadius d.retained b m)
    (hDeltaPow : b.deltaPow = δ ^ (k + 1))
    (hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity
      (fun j => Kakeya.unitTube (center j) (direction j) δ) x ^
      (((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ∂μ) ^
      (((((k + 2 : ℕ) : ℝ) - 1) / ((k + 2 : ℕ) : ℝ))) ≤
      ((2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) *
        paper46EndpointBudget μ
          (fun j => Kakeya.unitTube (center j) (direction j) δ)
          (k + 2)
          (d.retained.toBallLocalized μ (k + 2) b).toRetainedDyadicData
          a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((((k + 2 : ℕ) : ℝ) - 1) / ((k + 2 : ℕ) : ℝ))) := by
  exact full_conditional_kakeya_of_paper46_twoRadius μ
    (fun j => Kakeya.unitTube (center j) (direction j) δ)
    (k + 2) (by omega) d.retained b
    (ConcreteTwoRadiusGreedy.ofCanonicalVitaliEuclidean μ center direction
      δ hδ g d b hN hCanonical hT hv hDom hRadius hDeltaPow hCgeom) a


end Kakeya.Ninety21
