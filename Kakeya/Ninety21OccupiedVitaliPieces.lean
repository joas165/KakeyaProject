module

public import Kakeya.Ninety21TwoRadiusEndpoint

/-!
# Retained pieces from occupied Vitali balls

The radius-`R` intersections of the greedy gains with a tube-wise disjoint
Vitali selection determine the retained labels. Tubes with no occupied selected
ball contribute no retained label. Radius-`3R` enlargements remain the covering
sets in the analytic endpoint.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T : Type*} [MeasurableSpace X] [Fintype T]

/-- A localization index is occupied when its radius-`R` ball meets the gain. -/
noncomputable def ConcreteTubeBallGeometry.occupiedVitaliIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) :
    Finset (Fin (g.ballCount m)) := by
  classical
  exact (S m j).filter (fun i => (g.gain m j ∩ g.ball m i).Nonempty)

/-- Each occupied index gives a nonempty greedy-gain localization. -/
theorem ConcreteTubeBallGeometry.occupiedVitali_nonempty
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T)
    (i : Fin (g.ballCount m))
    (hi : i ∈ g.occupiedVitaliIndices S m j) :
    (g.gain m j ∩ g.ball m i).Nonempty := by
  exact (Finset.mem_filter.mp hi).2

/-- Removing candidate balls that do not meet their greedy gain
preserves the original radius-`R` localization cover. -/
theorem ConcreteTubeBallGeometry.occupiedCandidates_cover
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (L : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (U : Set X)
    (hCover : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ L m j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ g.ball m i)) :
    U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ g.occupiedVitaliIndices L m j,
      (((tubes j ∩ g.gain m j) ∩
        Kakeya.Eighty4.concreteDyadicBand tubes m) ∩ g.ball m i) := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hCover hx)
  obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
  obtain ⟨hiL, hxi⟩ := Set.mem_iUnion.mp hi
  have hOccupied : (g.gain m j ∩ g.ball m i).Nonempty :=
    ⟨x, ⟨hxi.1.1.2, hxi.2⟩⟩
  have hiOcc : i ∈ g.occupiedVitaliIndices L m j :=
    Finset.mem_filter.mpr ⟨hiL, hOccupied⟩
  exact Set.mem_iUnion.mpr ⟨j,
    Set.mem_iUnion.mpr ⟨hjB,
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiOcc, hxi⟩⟩⟩⟩

/-- Every Vitali subfamily selected from occupied candidates has
nonempty radius-`R` gain intersections. -/
theorem ConcreteTubeBallGeometry.vitali_subset_occupied
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (L S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hSub : ∀ j ∈ g.B m, S m j ⊆ g.occupiedVitaliIndices L m j) :
    ∀ j ∈ g.B m, ∀ i ∈ S m j,
      (g.gain m j ∩ g.ball m i).Nonempty := by
  intro j hj i hi
  exact g.occupiedVitali_nonempty L m j i (hSub j hj hi)

/-- The occupied radius-`R` tube–ball pairs form a finite indexed family. -/
noncomputable def ConcreteTubeBallGeometry.occupiedVitaliLabels
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Finset (T × Fin (g.ballCount m)) := by
  classical
  exact (Finset.univ : Finset (T × Fin (g.ballCount m))).filter
    (fun p => p.1 ∈ g.B m ∧ p.2 ∈ g.occupiedVitaliIndices S m p.1)

/-- Membership in the occupied tube–ball label family. -/
theorem ConcreteTubeBallGeometry.mem_occupiedVitaliLabels_iff
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (i : Fin (g.ballCount m)) :
    (j, i) ∈ g.occupiedVitaliLabels S m ↔
      j ∈ g.B m ∧ i ∈ g.occupiedVitaliIndices S m j := by
  classical
  simp only [ConcreteTubeBallGeometry.occupiedVitaliLabels,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every occupied label indexes a nonempty intersection. -/
theorem ConcreteTubeBallGeometry.occupiedVitaliLabel_nonempty
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : T × Fin (g.ballCount m))
    (hp : p ∈ g.occupiedVitaliLabels S m) :
    (g.gain m p.1 ∩ g.ball m p.2).Nonempty := by
  have hi : p.2 ∈ g.occupiedVitaliIndices S m p.1 :=
    (Finset.mem_filter.mp hp).2.2
  exact g.occupiedVitali_nonempty S m p.1 p.2 hi

/-- The gain-localized pieces are disjoint when the selected radius-`R`
balls are disjoint inside each tube fiber. -/
theorem ConcreteTubeBallGeometry.occupiedVitaliLabel_disjoint
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hVitali : ∀ j ∈ g.B m, ∀ i ∈ S m j, ∀ i' ∈ S m j,
      i ≠ i' → Disjoint (g.ball m i) (g.ball m i'))
    (p p' : T × Fin (g.ballCount m))
    (hp : p ∈ g.occupiedVitaliLabels S m)
    (hp' : p' ∈ g.occupiedVitaliLabels S m)
    (hne : p ≠ p') :
    Disjoint (g.gain m p.1 ∩ g.ball m p.2)
      (g.gain m p'.1 ∩ g.ball m p'.2) := by
  have hpm := (Finset.mem_filter.mp hp).2
  have hpm' := (Finset.mem_filter.mp hp').2
  by_cases hParent : p.1 = p'.1
  · have hBallNe : p.2 ≠ p'.2 := by
      intro heq
      apply hne
      exact Prod.ext hParent heq
    have hi : p.2 ∈ S m p.1 :=
      (Finset.mem_filter.mp hpm.2).1
    have hi' : p'.2 ∈ S m p.1 := by
      simpa only [hParent] using (Finset.mem_filter.mp hpm'.2).1
    have hd := hVitali p.1 hpm.1 p.2 hi p'.2 hi' hBallNe
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (Set.disjoint_left.mp hd) hx.2 hx'.2
  · have hd := g.gain_disjoint m p.1 p'.1 hParent
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact (Set.disjoint_left.mp hd) hx.1 hx'.1

/-- The active selected tubes are exactly those with an occupied ball. -/
noncomputable def ConcreteTubeBallGeometry.activeVitaliTubes
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : Finset T := by
  classical
  exact (g.B m).filter (fun j => (g.occupiedVitaliIndices S m j).Nonempty)

/-- Restricting the selected tubes to those with occupied Vitali balls
cannot increase the selected-tube budget. -/
theorem ConcreteTubeBallGeometry.activeVitaliTubes_card_le
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (g.activeVitaliTubes S m).card ≤ (g.B m).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The distinguished index is chosen from the occupied radius-`R` balls. -/
noncomputable def ConcreteTubeBallGeometry.firstOccupiedVitaliBall
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : {j : T // j ∈ g.activeVitaliTubes S m}) :
    Fin (g.ballCount m) := by
  have h : (g.occupiedVitaliIndices S m j.val).Nonempty :=
    (Finset.mem_filter.mp j.property).2
  exact Classical.choose h

/-- The distinguished index meets the greedy gain. -/
theorem ConcreteTubeBallGeometry.firstOccupiedVitaliBall_mem
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : {j : T // j ∈ g.activeVitaliTubes S m}) :
    g.firstOccupiedVitaliBall S m j ∈ g.occupiedVitaliIndices S m j.val := by
  have h : (g.occupiedVitaliIndices S m j.val).Nonempty :=
    (Finset.mem_filter.mp j.property).2
  exact Classical.choose_spec h

/-- Restrict the original selected labels to tubes having an occupied
Vitali ball and choose one such ball per tube. -/
noncomputable def ConcreteTubeBallGeometry.occupiedVitaliBase
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m))) :
    ConcreteTubeBallGeometry tubes := {
  g with
  B := g.activeVitaliTubes S
  P := fun _ => ∅
  hChosen := by
    intro m j hj
    exact g.hChosen m j (Finset.mem_filter.mp hj).1
  hPSelected := by
    intro m p hp
    simp at hp
  hPBall := by
    intro m p hp
    simp at hp
  selectedBall := fun m j => g.firstOccupiedVitaliBall S m j
}

/-- The remaining labels are the occupied Vitali pairs other than the
selected ball of their parent tube. The trimming is the identity because
the greedy gains and the selected balls are already disjoint. -/
noncomputable def ConcreteTubeBallGeometry.withOccupiedVitaliPieces
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m))) :
    ConcreteTubeBallGeometry tubes := by
  classical
  let base := g.occupiedVitaliBase S
  let S' : ∀ m, T → Finset (Fin (base.ballCount m)) :=
    fun m j => g.occupiedVitaliIndices S m j
  exact { (base.withVitaliPairs S') with trim := fun _ _ _ => Set.univ }

/-- Passing to occupied labels does not alter the ordered greedy gains. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitaliPieces_greedyQ
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (k : ℕ) :
    (g.withOccupiedVitaliPieces S).greedyQ m k = g.greedyQ m k := rfl

/-- On an active selected tube, the new geometry uses the original greedy gain. -/
theorem ConcreteTubeBallGeometry.occupiedVitali_gain_eq
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ (g.withOccupiedVitaliPieces S).B m) :
    (g.withOccupiedVitaliPieces S).gain m j = g.gain m j := by
  have hjActive : j ∈ g.activeVitaliTubes S m := by
    change j ∈ g.activeVitaliTubes S m at hj
    exact hj
  have hjOld : j ∈ g.B m := (Finset.mem_filter.mp hjActive).1
  simp [ConcreteTubeBallGeometry.gain,
    ConcreteTubeBallGeometry.withOccupiedVitaliPieces,
    ConcreteTubeBallGeometry.withVitaliPairs,
    ConcreteTubeBallGeometry.occupiedVitaliBase, hjActive, hjOld]

/-- The original greedy gain belongs to its parent tube. -/
theorem ConcreteTubeBallGeometry.gain_subset_parentTube
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) :
    g.gain m j ⊆ tubes j := by
  by_cases hj : j ∈ g.B m
  · intro x hx
    have hGain : x ∈ Kakeya.Eighty4.concreteGreedyGain tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.chosen m) (g.stage m j) := by
      simpa [ConcreteTubeBallGeometry.gain, hj] using hx
    have ht := Kakeya.Eighty4.concreteGreedyGain_subset_tube tubes
      (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (g.chosen m) (g.stage m j) hGain
    rw [g.hChosen m j hj] at ht
    exact ht
  · simp [ConcreteTubeBallGeometry.gain, hj]

/-- The original greedy gain belongs to the dyadic level. -/
theorem ConcreteTubeBallGeometry.gain_subset_dyadicLevel
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) :
    g.gain m j ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m := by
  by_cases hj : j ∈ g.B m
  · simpa [ConcreteTubeBallGeometry.gain, hj] using
      (Kakeya.Eighty4.concreteGreedyGain_subset_level tubes
        (Kakeya.Eighty4.concreteDyadicBand tubes m)
        (g.chosen m) (g.stage m j))
  · simp [ConcreteTubeBallGeometry.gain, hj]


/-- A gain–ball intersection is a nonempty retained piece when the trimming
set is the whole space. -/
theorem ConcreteTubeBallGeometry.piece_nonempty_of_gain_ball
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})
    (hTrim : g.trim m (g.tubeOf m s) (g.ballOf m s) = Set.univ)
    (hOcc : (g.gain m (g.tubeOf m s) ∩ g.ball m (g.ballOf m s)).Nonempty) :
    (g.piece m s).Nonempty := by
  obtain ⟨x, hxGain, hxBall⟩ := hOcc
  refine ⟨x, ?_⟩
  change x ∈ ((((tubes (g.tubeOf m s) ∩ g.gain m (g.tubeOf m s)) ∩
    Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
    g.ball m (g.ballOf m s)) ∩ g.trim m (g.tubeOf m s) (g.ballOf m s))
  refine ⟨⟨⟨⟨g.gain_subset_parentTube m (g.tubeOf m s) hxGain,
    hxGain⟩, g.gain_subset_dyadicLevel m (g.tubeOf m s) hxGain⟩,
    hxBall⟩, ?_⟩
  simp [hTrim]

/-- With identity trimming, a retained piece is exactly its greedy-gain
intersection with the radius-`R` localization ball. -/
theorem ConcreteTubeBallGeometry.piece_eq_gain_ball_of_univ_trim
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})
    (hTrim : g.trim m (g.tubeOf m s) (g.ballOf m s) = Set.univ) :
    g.piece m s = g.gain m (g.tubeOf m s) ∩ g.ball m (g.ballOf m s) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨g.piece_subset_gain m s hx, g.piece_subset_ball m s hx⟩
  · intro x hx
    change x ∈ ((((tubes (g.tubeOf m s) ∩ g.gain m (g.tubeOf m s)) ∩
      Kakeya.Eighty4.concreteDyadicBand tubes m) ∩
      g.ball m (g.ballOf m s)) ∩ g.trim m (g.tubeOf m s) (g.ballOf m s))
    exact ⟨⟨⟨⟨g.gain_subset_parentTube m (g.tubeOf m s) hx.1,
      hx.1⟩, g.gain_subset_dyadicLevel m (g.tubeOf m s) hx.1⟩,
      hx.2⟩, by simp [hTrim]⟩

/-- The pieces of the generated geometry are precisely the original
greedy-gain localizations. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitaliPieces_piece_eq
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ (g.withOccupiedVitaliPieces S).B m} ⊕
      {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m}) :
    (g.withOccupiedVitaliPieces S).piece m s =
      g.gain m ((g.withOccupiedVitaliPieces S).tubeOf m s) ∩
        g.ball m ((g.withOccupiedVitaliPieces S).ballOf m s) := by
  let g' := g.withOccupiedVitaliPieces S
  have hParent : g'.tubeOf m s ∈ g'.B m := by
    cases s with
    | inl r => exact r.property
    | inr p => exact g'.hPSelected m p.val p.property
  have hTrim : g'.trim m (g'.tubeOf m s) (g'.ballOf m s) =
      (Set.univ : Set X) := rfl
  rw [g'.piece_eq_gain_ball_of_univ_trim m s hTrim]
  rw [g.occupiedVitali_gain_eq S m (g'.tubeOf m s) hParent]
  rfl

/-- Every retained piece of the occupied Vitali construction is nonempty. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitaliPieces_nonempty
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ (g.withOccupiedVitaliPieces S).B m} ⊕
      {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m}) :
    ((g.withOccupiedVitaliPieces S).piece m s).Nonempty := by
  classical
  let g' := g.withOccupiedVitaliPieces S
  have hParent : g'.tubeOf m s ∈ g'.B m := by
    cases s with
    | inl r => exact r.property
    | inr p => exact g'.hPSelected m p.val p.property
  have hGainEq : g'.gain m (g'.tubeOf m s) =
      g.gain m (g'.tubeOf m s) :=
    g.occupiedVitali_gain_eq S m (g'.tubeOf m s) hParent
  have hOcc :
      (g.gain m (g'.tubeOf m s) ∩ g.ball m (g'.ballOf m s)).Nonempty := by
    cases s with
    | inl r =>
      have hi : g.firstOccupiedVitaliBall S m r ∈
          g.occupiedVitaliIndices S m r.val :=
        g.firstOccupiedVitaliBall_mem S m r
      have hn := g.occupiedVitali_nonempty S m r.val
        (g.firstOccupiedVitaliBall S m r) hi
      change (g.gain m r.val ∩
        g.ball m (g.firstOccupiedVitaliBall S m r)).Nonempty
      exact hn
    | inr p =>
      have hp : p.val ∈
          (g.occupiedVitaliBase S).vitaliPairs
            (fun m j => g.occupiedVitaliIndices S m j) m := p.property
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨hj, hi, hOther⟩ := ha
      have hn := g.occupiedVitali_nonempty S m a.1 a.2 hi
      have ht : a.1 = p.val.1 := congrArg Prod.fst heq
      have hb : a.2 =
          (⟨p.val.2, g'.hPBall m p.val p.property⟩ :
            Fin (g.ballCount m)) := Fin.ext (congrArg Prod.snd heq)
      change (g.gain m p.val.1 ∩
        g.ball m (⟨p.val.2, g'.hPBall m p.val p.property⟩ :
          Fin (g.ballCount m))).Nonempty
      rw [← ht, ← hb]
      exact hn
  have hOcc' :
      (g'.gain m (g'.tubeOf m s) ∩ g'.ball m (g'.ballOf m s)).Nonempty := by
    rw [hGainEq]
    exact hOcc
  have hTrim : g'.trim m (g'.tubeOf m s) (g'.ballOf m s) =
      (Set.univ : Set X) := rfl
  exact g'.piece_nonempty_of_gain_ball m s hTrim hOcc'


/-- A remaining pair never repeats its parent's distinguished ball. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitali_pairBall_ne_selected
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m}) :
    (g.withOccupiedVitaliPieces S).ballOf m (Sum.inr p) ≠
      (g.withOccupiedVitaliPieces S).selectedBall m
        ⟨p.val.1, (g.withOccupiedVitaliPieces S).hPSelected m p.val p.property⟩ := by
  classical
  let base := g.occupiedVitaliBase S
  let g' := g.withOccupiedVitaliPieces S
  have hp : p.val ∈ base.vitaliPairs
      (fun m j => g.occupiedVitaliIndices S m j) m := p.property
  obtain ⟨a, ha, hPair⟩ := Finset.mem_image.mp hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨hj, hi, hne⟩ := ha
  have ht : a.1 = p.val.1 := congrArg Prod.fst hPair
  have hBall : a.2 = g'.ballOf m (Sum.inr p) :=
    Fin.ext (congrArg Prod.snd hPair)
  have hSubtype : (⟨a.1, hj⟩ : {r : T // r ∈ base.B m}) =
      (⟨p.val.1, g'.hPSelected m p.val p.property⟩ :
        {r : T // r ∈ base.B m}) := Subtype.ext ht
  have hChosen : base.selectedBall m ⟨a.1, hj⟩ =
      g'.selectedBall m
        ⟨p.val.1, g'.hPSelected m p.val p.property⟩ := by
    exact congrArg (base.selectedBall m) hSubtype
  intro heq
  exact hne (hBall.trans (heq.trans hChosen.symm))

/-- A retained label is uniquely determined by its parent tube and ball. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitali_label_injective
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Function.Injective
      (fun s : {r : T // r ∈ (g.withOccupiedVitaliPieces S).B m} ⊕
          {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m} =>
        ((g.withOccupiedVitaliPieces S).tubeOf m s,
          (g.withOccupiedVitaliPieces S).ballOf m s)) := by
  classical
  let g' := g.withOccupiedVitaliPieces S
  intro s t hEq
  cases s with
  | inl r =>
    cases t with
    | inl r' =>
      have hTube : r.val = r'.val := congrArg Prod.fst hEq
      exact congrArg Sum.inl (Subtype.ext hTube)
    | inr p =>
      have hTube : r.val = p.val.1 := congrArg Prod.fst hEq
      have hBall : g'.selectedBall m r = g'.ballOf m (Sum.inr p) :=
        congrArg Prod.snd hEq
      have hR : r =
          (⟨p.val.1, g'.hPSelected m p.val p.property⟩ :
            {r : T // r ∈ g'.B m}) := Subtype.ext hTube
      rw [hR] at hBall
      exact False.elim ((g.withOccupiedVitali_pairBall_ne_selected S m p)
        hBall.symm)
  | inr p =>
    cases t with
    | inl r =>
      have hTube : p.val.1 = r.val := congrArg Prod.fst hEq
      have hBall : g'.ballOf m (Sum.inr p) = g'.selectedBall m r :=
        congrArg Prod.snd hEq
      have hR : r =
          (⟨p.val.1, g'.hPSelected m p.val p.property⟩ :
            {r : T // r ∈ g'.B m}) := Subtype.ext hTube.symm
      rw [hR] at hBall
      exact False.elim ((g.withOccupiedVitali_pairBall_ne_selected S m p)
        hBall)
    | inr p' =>
      have hPair :
          (g'.tubeOf m (Sum.inr p), g'.ballOf m (Sum.inr p)) =
          (g'.tubeOf m (Sum.inr p'), g'.ballOf m (Sum.inr p')) := hEq
      have hTube : p.val.1 = p'.val.1 := by
        exact congrArg
          (fun z : T × Fin (g.ballCount m) => z.1) hPair
      have hFin : g'.ballOf m (Sum.inr p) =
          g'.ballOf m (Sum.inr p') := by
        exact congrArg
          (fun z : T × Fin (g.ballCount m) => z.2) hPair
      have hIndex : p.val.2 = p'.val.2 := congrArg Fin.val hFin
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hTube hIndex))

/-- Every retained label corresponds to an occupied tube–ball pair. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitali_label_mem
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (s : {r : T // r ∈ (g.withOccupiedVitaliPieces S).B m} ⊕
      {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m}) :
    ((g.withOccupiedVitaliPieces S).tubeOf m s,
      (g.withOccupiedVitaliPieces S).ballOf m s) ∈
      g.occupiedVitaliLabels S m := by
  classical
  let g' := g.withOccupiedVitaliPieces S
  cases s with
  | inl r =>
    have hj : r.val ∈ g.B m := (Finset.mem_filter.mp r.property).1
    have hi := g.firstOccupiedVitaliBall_mem S m r
    change (r.val, g.firstOccupiedVitaliBall S m r) ∈
      g.occupiedVitaliLabels S m
    simp only [ConcreteTubeBallGeometry.occupiedVitaliLabels,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hj, hi⟩
  | inr p =>
    have hp : p.val ∈
        (g.occupiedVitaliBase S).vitaliPairs
          (fun m j => g.occupiedVitaliIndices S m j) m := p.property
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨hj, hi, hOther⟩ := ha
    have ht : a.1 = p.val.1 := congrArg Prod.fst heq
    have hb : a.2 = g'.ballOf m (Sum.inr p) :=
      Fin.ext (congrArg Prod.snd heq)
    have hjOriginal : p.val.1 ∈ g.B m := by
      have hjActive : a.1 ∈ g.activeVitaliTubes S m := hj
      rw [ht] at hjActive
      exact (Finset.mem_filter.mp hjActive).1
    have hi' : g'.ballOf m (Sum.inr p) ∈
        g.occupiedVitaliIndices S m p.val.1 := by
      rw [← ht, ← hb]
      exact hi
    change ((p.val.1, g'.ballOf m (Sum.inr p)) :
      T × Fin (g.ballCount m)) ∈ g.occupiedVitaliLabels S m
    exact (g.mem_occupiedVitaliLabels_iff S m p.val.1
      (g'.ballOf m (Sum.inr p))).2 ⟨hjOriginal, hi'⟩

/-- All retained pieces are disjoint for a tube-wise Vitali selection. -/
theorem ConcreteTubeBallGeometry.withOccupiedVitaliPieces_disjoint
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hVitali : ∀ j ∈ g.B m, ∀ i ∈ S m j, ∀ i' ∈ S m j,
      i ≠ i' → Disjoint (g.ball m i) (g.ball m i'))
    (s t : {r : T // r ∈ (g.withOccupiedVitaliPieces S).B m} ⊕
      {p : T × ℕ // p ∈ (g.withOccupiedVitaliPieces S).P m})
    (hne : s ≠ t) :
    Disjoint ((g.withOccupiedVitaliPieces S).piece m s)
      ((g.withOccupiedVitaliPieces S).piece m t) := by
  let g' := g.withOccupiedVitaliPieces S
  let pair := fun u : {r : T // r ∈ g'.B m} ⊕
      {p : T × ℕ // p ∈ g'.P m} =>
    (g'.tubeOf m u, g'.ballOf m u)
  have hDistinct : pair s ≠ pair t := by
    intro hEq
    exact hne (g.withOccupiedVitali_label_injective S m hEq)
  have hs : pair s ∈ g.occupiedVitaliLabels S m :=
    g.withOccupiedVitali_label_mem S m s
  have ht : pair t ∈ g.occupiedVitaliLabels S m :=
    g.withOccupiedVitali_label_mem S m t
  have hd := g.occupiedVitaliLabel_disjoint S m hVitali (pair s) (pair t)
    hs ht hDistinct
  rw [g.withOccupiedVitaliPieces_piece_eq S m s,
    g.withOccupiedVitaliPieces_piece_eq S m t]
  exact hd

/-- A radius-`R` Vitali index with nonempty gain intersection is represented
by the new selected or remaining retained labels. -/
theorem ConcreteTubeBallGeometry.occupiedVitali_mem_coverIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m)
    (i : Fin (g.ballCount m)) (hi : i ∈ S m j)
    (hOccupied : (g.gain m j ∩ g.ball m i).Nonempty) :
    i ∈ (g.withOccupiedVitaliPieces S).coverIndices m j := by
  classical
  let g' := g.withOccupiedVitaliPieces S
  have hiOcc : i ∈ g.occupiedVitaliIndices S m j :=
    Finset.mem_filter.mpr ⟨hi, hOccupied⟩
  have hjActive : j ∈ g.activeVitaliTubes S m :=
    Finset.mem_filter.mpr ⟨hj, ⟨i, hiOcc⟩⟩
  have hj' : j ∈ g'.B m := hjActive
  by_cases heq : i = g'.selectedBall m ⟨j, hj'⟩
  · rw [heq]
    exact g'.selectedBall_mem_coverIndices m ⟨j, hj'⟩
  · have hne : i ≠
        (g.occupiedVitaliBase S).selectedBall m ⟨j, hjActive⟩ := heq
    have hp : (j, i.val) ∈ g'.P m :=
      (g.occupiedVitaliBase S).vitaliPairs_contains
        (fun m j => g.occupiedVitaliIndices S m j)
        m j hjActive i hiOcc hne
    let p : {p : T × ℕ // p ∈ g'.P m} := ⟨(j, i.val), hp⟩
    have hm := g'.pairBall_mem_coverIndices m p
    have hIndex :
        (⟨p.val.2, g'.hPBall m p.val p.property⟩ :
          Fin (g'.ballCount m)) = i := Fin.ext rfl
    rw [hIndex] at hm
    exact hm

/-- The original selected triple-radius cover transfers to the occupied
retained indices. It does not require coverage by radius-`R` pieces. -/
theorem ConcreteTubeBallGeometry.occupiedVitali_cover_transfer
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (E : T → Fin (g.ballCount m) → Set X) (U : Set X)
    (hOccupied : ∀ j ∈ g.B m, ∀ i ∈ S m j,
      (g.gain m j ∩ g.ball m i).Nonempty)
    (hCover : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ S m j, E j i) :
    U ⊆ ⋃ j ∈ (g.withOccupiedVitaliPieces S).B m,
      ⋃ i ∈ (g.withOccupiedVitaliPieces S).coverIndices m j, E j i := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hCover hx)
  obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  have hMem := g.occupiedVitali_mem_coverIndices S m j hjB i hiS
    (hOccupied j hjB i hiS)
  have hiOcc : i ∈ g.occupiedVitaliIndices S m j :=
    Finset.mem_filter.mpr ⟨hiS, hOccupied j hjB i hiS⟩
  have hjActive : j ∈ (g.withOccupiedVitaliPieces S).B m :=
    Finset.mem_filter.mpr ⟨hjB, ⟨i, hiOcc⟩⟩
  exact Set.mem_iUnion.mpr ⟨j,
    Set.mem_iUnion.mpr ⟨hjActive,
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hMem, hxi⟩⟩⟩⟩

/-- The two-radius index budget holds for the occupied retained family. -/
theorem ConcreteTubeBallGeometry.occupiedVitali_index_budget
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (∑ j ∈ (g.withOccupiedVitaliPieces S).B m,
      ((g.withOccupiedVitaliPieces S).coverIndices m j).card) ≤
      ((g.withOccupiedVitaliPieces S).B m).card +
      ((g.withOccupiedVitaliPieces S).P m).card := by
  exact (g.withOccupiedVitaliPieces S).coverIndices_card_budget_nat m


/-- Populate the two-radius endpoint from occupied Vitali indices. The
covering sets use radius `3R`; the retained pieces and the incidence balls
continue to use radius `R`. -/
noncomputable def ConcreteTwoRadiusGreedy.ofOccupiedVitali
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (b : ConcreteTubeBallBounds μ tubes n (g.withOccupiedVitaliPieces S))
    (hT : ∀ j, MeasurableSet (tubes j))
    (hStep : ∀ m k,
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
        (Fintype.card T : ℝ)) *
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k)
    (centers : ∀ m, Fin (g.ballCount m) → X)
    (hBall : ∀ m i,
      g.ball m i = Metric.ball (centers m i)
        (twoRadiusRadius (g.withOccupiedVitaliPieces S) b m))
    (hOccupied : ∀ m j, j ∈ g.B m → ∀ i, i ∈ S m j →
      (g.gain m j ∩ g.ball m i).Nonempty)
    (hCover : ∀ m,
      Kakeya.Eighty4.greedyUnion (g.greedyQ m)
        ⌈(Fintype.card T : ℝ) /
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ j ∈ g.B m, ⋃ i ∈ S m j,
        tubes j ∩ Metric.ball (centers m i)
          (3 * twoRadiusRadius (g.withOccupiedVitaliPieces S) b m))
    (hTripleCost : ∀ m j i,
      j ∈ (g.withOccupiedVitaliPieces S).B m →
      i ∈ (g.withOccupiedVitaliPieces S).coverIndices m j →
      Kakeya.Conditional.mass μ
        (tubes j ∩ Metric.ball (centers m i)
          (3 * twoRadiusRadius (g.withOccupiedVitaliPieces S) b m)) ≤
      b.C * b.deltaPow *
        twoRadiusRadius (g.withOccupiedVitaliPieces S) b m) :
    ConcreteTwoRadiusGreedy μ tubes n (g.withOccupiedVitaliPieces S) b := by
  refine {
    hT := hT
    hStep := hStep
    centers := centers
    hBall := hBall
    hVitali := ?_
    hTripleCost := hTripleCost
  }
  intro m
  exact g.occupiedVitali_cover_transfer S m
    (fun j i => tubes j ∩ Metric.ball (centers m i)
      (3 * twoRadiusRadius (g.withOccupiedVitaliPieces S) b m))
    (Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
    (hOccupied m) (hCover m)

end Kakeya.Ninety21
