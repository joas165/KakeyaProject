module

public import Kakeya.Ninety21RetainedCoverage

/-!
# Vitali indexing by retained tube–ball labels

The cover indices are the ball indices represented by the retained labels with a
specified parent tube. Their number is bounded by the total retained-label count.
A Vitali subfamily may also be used to construct the remaining pair labels.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T : Type*} [MeasurableSpace X] [Fintype T]

/-- Ball indices represented by retained labels with parent `j`. -/
noncomputable def ConcreteTubeBallGeometry.coverIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (j : T) :
    Finset (Fin (g.ballCount m)) := by
  classical
  exact ((Finset.univ : Finset
      ({r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})).filter
        (fun s => g.tubeOf m s = j)).image (g.ballOf m)

/-- The designated ball of a selected tube belongs to its cover indices. -/
theorem ConcreteTubeBallGeometry.selectedBall_mem_coverIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : {j : T // j ∈ g.B m}) :
    g.selectedBall m j ∈ g.coverIndices m j.val := by
  classical
  unfold ConcreteTubeBallGeometry.coverIndices
  apply Finset.mem_image.mpr
  refine ⟨Sum.inl j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  rfl

/-- The ball of a remaining pair label belongs to its parent's cover indices. -/
theorem ConcreteTubeBallGeometry.pairBall_mem_coverIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {p : T × ℕ // p ∈ g.P m}) :
    (⟨p.val.2, g.hPBall m p.val p.property⟩ : Fin (g.ballCount m)) ∈
      g.coverIndices m p.val.1 := by
  classical
  unfold ConcreteTubeBallGeometry.coverIndices
  apply Finset.mem_image.mpr
  refine ⟨Sum.inr p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  rfl

/-- Counting the represented ball indices uses no geometric assumptions. -/
theorem ConcreteTubeBallGeometry.coverIndices_card_budget_nat
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (∑ j ∈ g.B m, (g.coverIndices m j).card) ≤
      (g.B m).card + (g.P m).card := by
  classical
  let L := ({r : T // r ∈ g.B m} ⊕ {p : T × ℕ // p ∈ g.P m})
  let fiber : T → Finset L := fun j =>
    (Finset.univ : Finset L).filter (fun s => g.tubeOf m s = j)
  have hImage : ∀ j, (g.coverIndices m j).card ≤ (fiber j).card := by
    intro j
    change ((fiber j).image (g.ballOf m)).card ≤ (fiber j).card
    exact Finset.card_image_le
  have hParent : ∀ s : L, g.tubeOf m s ∈ g.B m := by
    intro s
    cases s with
    | inl r => exact r.property
    | inr p => exact g.hPSelected m p.val p.property
  have hTotal : (∑ j ∈ g.B m, (fiber j).card) = Fintype.card L := by
    calc
      (∑ j ∈ g.B m, (fiber j).card) =
          ((Finset.univ : Finset L).filter
            (fun s => g.tubeOf m s ∈ g.B m)).card := by
            simpa only [fiber] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (Finset.univ : Finset L) (g.B m) (g.tubeOf m))
      _ = (Finset.univ : Finset L).card := by
            congr 1
            ext s
            simp [hParent s]
      _ = Fintype.card L := Finset.card_univ
  have hCard : Fintype.card L = (g.B m).card + (g.P m).card := by
    simp [L, Fintype.card_sum]
  calc
    _ ≤ ∑ j ∈ g.B m, (fiber j).card :=
      Finset.sum_le_sum (fun j _ => hImage j)
    _ = Fintype.card L := hTotal
    _ = (g.B m).card + (g.P m).card := hCard

/-- Real-valued cardinality budget for the two-radius endpoint. -/
theorem ConcreteTubeBallGeometry.coverIndices_card_budget
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (∑ j ∈ g.B m, ((g.coverIndices m j).card : ℝ)) ≤
      ((g.B m).card : ℝ) + ((g.P m).card : ℝ) := by
  exact_mod_cast g.coverIndices_card_budget_nat m

/-- Remaining tube–ball labels determined by a finite Vitali selection. -/
noncomputable def ConcreteTubeBallGeometry.vitaliPairs
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : Finset (T × ℕ) := by
  classical
  exact ((Finset.univ : Finset (T × Fin (g.ballCount m))).filter
    (fun p => ∃ hj : p.1 ∈ g.B m,
      p.2 ∈ S m p.1 ∧ p.2 ≠ g.selectedBall m ⟨p.1, hj⟩)).image
        (fun p => (p.1, p.2.val))

/-- Every generated pair belongs to a selected tube. -/
theorem ConcreteTubeBallGeometry.vitaliPairs_parent
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : T × ℕ) (hp : p ∈ g.vitaliPairs S m) : p.1 ∈ g.B m := by
  classical
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hp
  obtain ⟨hj, _, _⟩ := (Finset.mem_filter.mp ha).2
  have heq1 : a.1 = p.1 := congrArg Prod.fst heq
  exact heq1 ▸ hj

/-- Every generated pair refers to a valid localization-ball index. -/
theorem ConcreteTubeBallGeometry.vitaliPairs_ball
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : T × ℕ) (hp : p ∈ g.vitaliPairs S m) : p.2 < g.ballCount m := by
  classical
  obtain ⟨a, _, heq⟩ := Finset.mem_image.mp hp
  have heq2 : a.2.val = p.2 := congrArg Prod.snd heq
  exact heq2 ▸ a.2.isLt

/-- Every selected non-designated Vitali index has a generated pair label. -/
theorem ConcreteTubeBallGeometry.vitaliPairs_contains
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m) (i : Fin (g.ballCount m))
    (hi : i ∈ S m j)
    (hne : i ≠ g.selectedBall m ⟨j, hj⟩) :
    (j, i.val) ∈ g.vitaliPairs S m := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  exact ⟨hj, hi, hne⟩

/-- Use the Vitali selection itself to index all remaining pairs. -/
noncomputable def ConcreteTubeBallGeometry.withVitaliPairs
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m))) :
    ConcreteTubeBallGeometry tubes := {
  g with
  P := g.vitaliPairs S
  hPSelected := g.vitaliPairs_parent S
  hPBall := g.vitaliPairs_ball S
}

/-- Selected Vitali balls are represented by the constructed retained labels. -/
theorem ConcreteTubeBallGeometry.vitali_mem_coverIndices
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (j : T) (hj : j ∈ g.B m)
    (i : Fin (g.ballCount m)) (hi : i ∈ S m j) :
    i ∈ (g.withVitaliPairs S).coverIndices m j := by
  classical
  by_cases heq : i = g.selectedBall m ⟨j, hj⟩
  · subst i
    exact (g.withVitaliPairs S).selectedBall_mem_coverIndices m ⟨j, hj⟩
  · have hp : (j, i.val) ∈ (g.withVitaliPairs S).P m :=
      g.vitaliPairs_contains S m j hj i hi heq
    let p : {p : T × ℕ // p ∈ (g.withVitaliPairs S).P m} :=
      ⟨(j, i.val), hp⟩
    have hm := (g.withVitaliPairs S).pairBall_mem_coverIndices m p
    have hEq :
        (⟨p.val.2,
          (g.withVitaliPairs S).hPBall m p.val p.property⟩ :
          Fin ((g.withVitaliPairs S).ballCount m)) = i := Fin.ext rfl
    rw [hEq] at hm
    exact hm

/-- A cover by the selected Vitali indices transfers to the generated family. -/
theorem ConcreteTubeBallGeometry.vitali_cover_withPairs
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    (S : ∀ m, T → Finset (Fin (g.ballCount m)))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (E : T → Fin (g.ballCount m) → Set X) (U : Set X)
    (hCover : U ⊆ ⋃ j ∈ g.B m, ⋃ i ∈ S m j, E j i) :
    U ⊆ ⋃ j ∈ (g.withVitaliPairs S).B m,
      ⋃ i ∈ (g.withVitaliPairs S).coverIndices m j, E j i := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hCover hx)
  obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  apply Set.mem_iUnion.mpr
  refine ⟨j, Set.mem_iUnion.mpr ⟨hjB, ?_⟩⟩
  exact Set.mem_iUnion.mpr
    ⟨i, Set.mem_iUnion.mpr ⟨g.vitali_mem_coverIndices S m j hjB i hiS, hxi⟩⟩

end Kakeya.Ninety21
