module

public import Kakeya.Ninety118FirstEquality

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal
open Classical

section

variable {T L P : Type*} [DecidableEq T] [LinearOrder L] [DecidableEq P]

/-- Global ordered tails equal the overlap sum over unordered pairs with the same parent. -/
def SecondOverlapEquality (R : Finset L) (I : L → Finset T) (parent : L → P) : Prop :=
  (∑ k ∈ Finset.Icc 2 R.card, ∑ i ∈ R, (orderedTail R I i k).card) =
    ∑ r ∈ R, ∑ s ∈ (R.filter (fun t => parent t = parent r)).filter (fun s => r < s),
      (I r ∩ I s).card

private theorem parent_tail_sum_eq_parent_overlap
    (R : Finset L) (I : L → Finset T) (parent : L → P) :
    (∑ k ∈ Finset.Icc 2 R.card, ∑ i ∈ R,
      (orderedTail (R.filter (fun r => parent r = parent i)) I i k).card) =
    ∑ r ∈ R, ∑ s ∈ (R.filter (fun t => parent t = parent r)).filter (fun s => r < s),
      (I r ∩ I s).card := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  let S := R.filter (fun r => parent r = parent i)
  have hiS : i ∈ S := Finset.mem_filter.mpr ⟨hi, rfl⟩
  rw [ordered_overlap_eq_sum_tails S I hiS]
  symm
  apply Finset.sum_subset
  · intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans (Finset.card_le_card (Finset.filter_subset _ R))⟩
  · intro k hk hkS
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    exact hkS (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_filter.mp hl).2.trans (Finset.card_le_card (Finset.filter_subset _ S))⟩)

/-- Each comparison tail is contained in the global tail. The second equality makes
their total cardinalities equal, so every individual cardinality is equal. -/
theorem global_tail_card_of_secondEquality
    (R : Finset L) (I : L → Finset T) (parent : L → P)
    (h : SecondOverlapEquality R I parent) {i : L} (hi : i ∈ R) {k : ℕ} (hk : 2 ≤ k) :
    (orderedTail R I i k).card =
      (orderedTail (R.filter (fun r => parent r = parent i)) I i k).card := by
  let S (i : L) := R.filter (fun r => parent r = parent i)
  have hle (i : L) (k : ℕ) :
      (orderedTail (S i) I i k).card ≤ (orderedTail R I i k).card := by
    apply Finset.card_le_card
    intro l hl
    obtain ⟨hlI, hn⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hlI, hn.trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))⟩
  by_cases hkr : k ≤ R.card
  · have hsum := (parent_tail_sum_eq_parent_overlap R I parent).trans h.symm
    have hlevel := (Finset.sum_eq_sum_iff_of_le (fun t _ =>
      Finset.sum_le_sum (fun j (_ : j ∈ R) => hle j t))).mp hsum k
      (Finset.mem_Icc.mpr ⟨hk, hkr⟩)
    exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hle j k)).mp hlevel i hi).symm
  · have hempty : orderedTail R I i k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact hkr ((Finset.mem_filter.mp hl).2.trans
        (Finset.card_le_card (Finset.filter_subset _ R)))
    exact le_antisymm (by rw [hempty]; simp) (hle i k)

end

namespace TubeFamily

variable {T : Type*} [Fintype T] [Nonempty T] {d : ℕ} {A : ℝ≥0} (f : TubeFamily T d A)

/-- The second equality at the large dyadic levels used by the endpoint. -/
noncomputable def SecondEqualityApplication : Prop := by
  classical
  exact ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    SecondOverlapEquality (Finset.univ : Finset Label)
      (incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val)))
      (fun i : Label => f.pieces.parent m i.val)

theorem overlapApplication_of_secondEquality (h : f.SecondEqualityApplication) :
    f.OverlapApplication (fixedParentTailConstant d A) := by
  classical
  intro m hq hr
  let := f.regularOrder m
  let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let I := incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val))
  let parent := fun i : Label => f.pieces.parent m i.val
  intro i hi k hk
  have hk2 : 2 ≤ k := by
    have hcap : 0 < binCapacity d := by unfold binCapacity; positivity
    unfold multipleThreshold at hk
    omega
  have he := global_tail_card_of_secondEquality Finset.univ I parent (h m hq hr) hi hk2
  change ((orderedTail Finset.univ I i k).card : ℝ) ≤ _
  rw [he]
  exact f.regular_tail_card_along_parent m i hk

theorem logarithmic_norm_bound_of_secondEquality (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    (h : f.SecondEqualityApplication) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A (fixedParentTailConstant d A) * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ :=
  f.logarithmic_norm_bound hd hN (f.overlapApplication_of_secondEquality h)

end TubeFamily
end Kakeya.Ninety109
