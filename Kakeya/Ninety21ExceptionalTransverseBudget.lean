module

public import Kakeya.Ninety21ExceptionalParentBudget
public import Kakeya.Ninety21ParentVitaliPacking
public import Kakeya.Ninety21TwoTubeTransverseGeometry

/-!
# Exceptional-piece counting by transverse original tubes

For a fixed selected parent tube, every exceptional piece meets more than
half of the original tubes. Counting the intersections with directions away
from the parent's direction bounds the number of exceptional localization
balls. The counted balls are the actual retained Vitali balls.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- A finite bipartite incidence budget with a small exceptional set of
right-hand vertices. -/
theorem transverse_finite_incidence_count
    {I T : Type*} [Fintype T]
    (r : T) (J : Finset I) (near : Finset T)
    (hit : I → T → Prop) (L : ℕ)
    (hNear : 4 * near.card ≤ Fintype.card T)
    (hLarge : ∀ i ∈ J,
      Fintype.card T < 2 * (Finset.univ.filter (hit i)).card)
    (hPair : ∀ ell ∉ near,
      (J.filter (fun i => hit i ell)).card ≤ L) :
    J.card ≤ 4 * L := by
  classical
  let U : Finset T := Finset.univ.filter (fun ell => ell ∉ near)
  have hSub (i : I) (hi : i ∈ J) :
      (Finset.univ.filter (hit i)).card ≤
        near.card + (U.filter (fun ell => hit i ell)).card := by
    have hsubset : Finset.univ.filter (hit i) ⊆
        near ∪ U.filter (fun ell => hit i ell) := by
      intro ell hell
      by_cases hn : ell ∈ near
      · exact Finset.mem_union.mpr (Or.inl hn)
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩,
            (Finset.mem_filter.mp hell).2⟩
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hLower (i : I) (hi : i ∈ J) :
      Fintype.card T ≤
        4 * (U.filter (fun ell => hit i ell)).card := by
    have hcard := hSub i hi
    have hlarge := hLarge i hi
    omega
  have hDouble :
      (∑ i ∈ J, (U.filter (fun ell => hit i ell)).card) =
      ∑ ell ∈ U, (J.filter (fun i => hit i ell)).card := by
    calc
      (∑ i ∈ J, (U.filter (fun ell => hit i ell)).card) =
          ∑ i ∈ J, ∑ ell ∈ U, if hit i ell then (1 : ℕ) else 0 := by
            simp [Finset.sum_boole]
      _ = ∑ ell ∈ U, ∑ i ∈ J,
          if hit i ell then (1 : ℕ) else 0 := by rw [Finset.sum_comm]
      _ = ∑ ell ∈ U, (J.filter (fun i => hit i ell)).card := by
        simp [Finset.sum_boole]
  have hSumLower :
      (Fintype.card T) * J.card ≤
        4 * (∑ i ∈ J, (U.filter (fun ell => hit i ell)).card) := by
    calc
      (Fintype.card T) * J.card = ∑ i ∈ J, Fintype.card T := by
        simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ J, 4 * (U.filter (fun ell => hit i ell)).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact hLower i hi
      _ = 4 * (∑ i ∈ J, (U.filter (fun ell => hit i ell)).card) := by
        simp [Finset.mul_sum]
  have hSumUpper :
      (∑ ell ∈ U, (J.filter (fun i => hit i ell)).card) ≤
        U.card * L := by
    calc
      (∑ ell ∈ U, (J.filter (fun i => hit i ell)).card) ≤
          ∑ ell ∈ U, L := by
            apply Finset.sum_le_sum
            intro ell hell
            exact hPair ell (Finset.mem_filter.mp hell).2
      _ = U.card * L := by simp
  have hU : U.card ≤ Fintype.card T :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by simp)
  have hTotal : Fintype.card T * J.card ≤
      Fintype.card T * (4 * L) := by
    calc
      Fintype.card T * J.card ≤
          4 * (∑ i ∈ J, (U.filter (fun ell => hit i ell)).card) := hSumLower
      _ = 4 * (∑ ell ∈ U, (J.filter (fun i => hit i ell)).card) := by rw [hDouble]
      _ ≤ 4 * (U.card * L) := Nat.mul_le_mul_left _ hSumUpper
      _ ≤ Fintype.card T * (4 * L) := by nlinarith
  have hN : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨r⟩
  nlinarith

/-- The localization ball of an exceptional retained piece meets every
original tube that meets that piece. -/
theorem exceptional_parent_ball_large_original_incidence
    {X T K : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (i : Fin (s.ballCount m))
    (hi : i ∈ paperExceptionalParentBallIndices μ tubes n s m r) :
    Fintype.card T <
      2 * (Finset.univ.filter (fun ell : T =>
        (s.ball m i ∩ tubes ell).Nonempty)).card := by
  classical
  obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
  have hpExc := (Finset.mem_filter.mp hp).1
  have hD := (mem_paperExceptionalPieces
    μ tubes n s.toRetainedDyadicData m p).mp hpExc
  have hsub :
      Finset.univ.filter (fun ell : T =>
        (s.retainedPiece m (Sum.inr p) ∩ tubes ell).Nonempty) ⊆
      Finset.univ.filter (fun ell : T =>
        (s.ball m i ∩ tubes ell).Nonempty) := by
    intro ell hell
    obtain ⟨x, hxP, hxTube⟩ := (Finset.mem_filter.mp hell).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨x, ?_, hxTube⟩⟩
    have hxBall := s.hSourceBall m (Sum.inr p) hxP
    rw [hpi] at hxBall
    exact hxBall
  have hc := Finset.card_le_card hsub
  have hDegree : paperOriginalTubeDegree
      μ tubes n s.toRetainedDyadicData m p ≤
      (Finset.univ.filter (fun ell : T =>
        (s.ball m i ∩ tubes ell).Nonempty)).card := by
    simpa only [paperOriginalTubeDegree] using hc
  omega

/-- The parent-wise exceptional-ball packing estimate follows from a
uniform two-tube incidence estimate outside a small angular cap. -/
theorem exceptional_parent_ball_packing_of_transverse_count
    {X T K : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (L : ℕ) (near : T → Finset T)
    (hNear : ∀ r ∈ s.B m,
      4 * (near r).card ≤ Fintype.card T)
    (hTransverse : ∀ r ∈ s.B m, ∀ ell ∉ near r,
      ((paperExceptionalParentBallIndices μ tubes n s m r).filter
        (fun i => (s.ball m i ∩ tubes ell).Nonempty)).card ≤ L) :
    ∀ r ∈ s.B m,
      (paperExceptionalParentBallIndices μ tubes n s m r).card ≤ 4 * L := by
  intro r hr
  exact transverse_finite_incidence_count r
    (paperExceptionalParentBallIndices μ tubes n s m r)
    (near r)
    (fun i ell => (s.ball m i ∩ tubes ell).Nonempty) L
    (hNear r hr)
    (fun i hi => exceptional_parent_ball_large_original_incidence
      μ tubes n s m r i hi)
    (hTransverse r hr)

/-- The exceptional budget from two-tube transverse incidence counts. -/
theorem exceptional_scaled_budget_of_transverse_count
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (L : ℕ) (near : T → Finset T)
    (hNear : ∀ r ∈ s.B m,
      4 * (near r).card ≤ Fintype.card T)
    (hTransverse : ∀ r ∈ s.B m, ∀ ell ∉ near r,
      ((paperExceptionalParentBallIndices μ tubes n s m r).filter
        (fun i => (s.ball m i ∩ tubes ell).Nonempty)).card ≤ L) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
      8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  have hPacking := exceptional_parent_ball_packing_of_transverse_count
    μ tubes n s m L near hNear hTransverse
  have hBudget := paper_exceptional_scaled_budget_of_pair_indexing
    μ tubes n s indexing m (4 * L) hPacking
  calc
    _ ≤ 2 * (4 * (L : ℝ)) * (Fintype.card T : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hBudget
    _ = 8 * (L : ℝ) * (Fintype.card T : ℝ) := by ring

/-- Every exceptional parent ball is a selected Vitali ball of that
original parent tube. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_parent_balls_selected
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (b : ConcreteTubeBallBounds μ tubes n d.retained)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (r : T) :
    paperExceptionalParentBallIndices μ tubes n
      (d.retained.toBallLocalized μ n b) m r ⊆ d.selected m r := by
  intro i hi
  obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
  have hr : (d.retained.toBallLocalized μ n b).parent m p = r :=
    (Finset.mem_filter.mp hp).2
  apply d.parent_associated_mem_selected m r i
  refine ⟨Sum.inr p, ?_, ?_⟩
  · exact hr
  · exact hpi

/-- The selected Vitali disjointness applies to distinct exceptional balls
attached to the same original parent. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_parent_balls_disjoint
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [Fintype T]
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (d : ConcreteGreedyVitaliCandidates tubes g)
    (b : ConcreteTubeBallBounds μ tubes n d.retained)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (hr : r ∈ g.B m)
    (i j : Fin (d.retained.ballCount m))
    (hi : i ∈ paperExceptionalParentBallIndices μ tubes n
      (d.retained.toBallLocalized μ n b) m r)
    (hj : j ∈ paperExceptionalParentBallIndices μ tubes n
      (d.retained.toBallLocalized μ n b) m r)
    (hij : i ≠ j) :
    Disjoint (d.retained.ball m i) (d.retained.ball m j) := by
  have hiSelected := d.exceptional_parent_balls_selected
    μ tubes n g b m r hi
  have hjSelected := d.exceptional_parent_balls_selected
    μ tubes n g b m r hj
  have hd := d.selected_disjoint m r hr i hiSelected j hjSelected hij
  simpa only [d.retained_ball_eq m i, d.retained_ball_eq m j] using hd


/-- Disjoint Vitali balls of one parent original tube obey the quantitative
two-transverse-tube count obtained from a Euclidean half-radius net. -/
theorem ConcreteGreedyVitaliCandidates.selected_transverse_pair_card_le
    {n : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space n)
    (δ θ : ℝ) (L : ℕ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r ell : T) (hr : r ∈ g.B m)
    (hδR : δ ≤ d.radius m) (hθ : 0 < θ)
    (hu : ‖direction r‖ = 1)
    (hTrans : TransverseDirections (direction r) (direction ell) θ)
    (hCover : ∀ c : Kakeya.Space n,
      ∃ Z : Finset (Kakeya.Space n), Z.card ≤ L ∧
        ∀ x : Kakeya.Space n,
          dist x c ≤ (4 + 8 / θ) * d.radius m →
            ∃ z ∈ Z, dist x z < d.radius m / 2) :
    ((d.selected m r).filter (fun i =>
      (g.ball m i ∩ Kakeya.unitTube (center ell) (direction ell) δ).Nonempty)).card
      ≤ L := by
  classical
  let J := (d.selected m r).filter (fun i =>
    (g.ball m i ∩ Kakeya.unitTube (center ell) (direction ell) δ).Nonempty)
  apply two_transverse_tubes_ball_count_of_cover
    (center r) (center ell) (direction r) (direction ell)
    δ (d.radius m) θ L (d.hRadius m) hδR hθ hu hTrans
    (d.centers m) J
  · intro i hi j hj hij
    have his : i ∈ d.selected m r := (Finset.mem_filter.mp hi).1
    have hjs : j ∈ d.selected m r := (Finset.mem_filter.mp hj).1
    simpa only [d.hBall m i, d.hBall m j] using
      (d.selected_disjoint m r hr i his j hjs hij)
  · intro i hi
    have his : i ∈ d.selected m r := (Finset.mem_filter.mp hi).1
    simpa only [d.hBall m i] using
      (d.selected_ball_meets_parent_tube m r hr i his)
  · intro i hi
    have hx := (Finset.mem_filter.mp hi).2
    simpa only [d.hBall m i] using hx
  · exact hCover

/-- Exceptional-piece counting for the actual occupied greedy–Vitali family.
The two geometric inputs are angular-cap counting and a uniform Euclidean
covering number; the remaining estimates follow from `selected_disjoint`
and the exact original-tube exceptional degree. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_transverse_geometry
    {n : ℕ} {T : Type*} [Fintype T]
    (μ : Measure (Kakeya.Space n))
    (center direction : T → Kakeya.Space n)
    (δ θ : ℝ) (L : ℕ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n d.retained)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hδR : δ ≤ d.radius m) (hθ : 0 < θ)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (near : T → Finset T)
    (hNear : ∀ r ∈ (d.retained.toBallLocalized μ n b).B m,
      4 * (near r).card ≤ Fintype.card T)
    (hParentSelected : ∀ r ∈ (d.retained.toBallLocalized μ n b).B m,
      r ∈ g.B m)
    (hTransverse : ∀ r ∈ (d.retained.toBallLocalized μ n b).B m,
      ∀ ell ∉ near r,
        TransverseDirections (direction r) (direction ell) θ)
    (hCover : ∀ c : Kakeya.Space n,
      ∃ Z : Finset (Kakeya.Space n), Z.card ≤ L ∧
        ∀ x : Kakeya.Space n,
          dist x c ≤ (4 + 8 / θ) * d.radius m →
            ∃ z ∈ Z, dist x z < d.radius m / 2) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ
        (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n
        (d.retained.toBallLocalized μ n b).toRetainedDyadicData m).card : ℝ) ≤
      8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  classical
  let tubes : T → Set (Kakeya.Space n) :=
    fun ell => Kakeya.unitTube (center ell) (direction ell) δ
  let s := d.retained.toBallLocalized μ n b
  have hBallEq (i : Fin (s.ballCount m)) :
      s.ball m i = g.ball m i := by
    change d.retained.ball m i = g.ball m i
    exact d.retained_ball_eq m i
  have hPair : ∀ r ∈ s.B m, ∀ ell ∉ near r,
      ((paperExceptionalParentBallIndices μ tubes n s m r).filter
        (fun i => (s.ball m i ∩ tubes ell).Nonempty)).card ≤ L := by
    intro r hr ell hEll
    let J := paperExceptionalParentBallIndices μ tubes n s m r
    have hJSelected : J ⊆ d.selected m r := by
      exact d.exceptional_parent_balls_selected μ tubes n g b m r
    have hSubset :
        J.filter (fun i => (s.ball m i ∩ tubes ell).Nonempty) ⊆
        (d.selected m r).filter (fun i => (g.ball m i ∩ tubes ell).Nonempty) := by
      intro i hi
      obtain ⟨hiJ, hiHit⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨hJSelected hiJ, ?_⟩
      rw [hBallEq i] at hiHit
      exact hiHit
    have hCount := d.selected_transverse_pair_card_le
      center direction δ θ L g m r ell
      (hParentSelected r hr) hδR hθ (hUnit r)
      (hTransverse r hr ell hEll) hCover
    exact (Finset.card_le_card hSubset).trans hCount
  have hPack := exceptional_parent_ball_packing_of_transverse_count
    μ tubes n s m L near hNear hPair
  have hBudget := paper_exceptional_scaled_budget_of_pair_indexing
    μ tubes n s (d.retained.pairIndexing μ n b) m (4 * L) hPack
  calc
    _ ≤ 2 * (4 * (L : ℝ)) * (Fintype.card T : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hBudget
    _ = 8 * (L : ℝ) * (Fintype.card T : ℝ) := by ring

end Kakeya.Ninety21
