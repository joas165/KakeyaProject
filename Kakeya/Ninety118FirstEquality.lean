module

public import Kakeya.Ninety109Endpoint

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal
open Classical

/-- Page 16, first equality. The later labels in every tail range over all of R. -/
theorem global_overlap_eq_sum_tails {T L : Type*} [DecidableEq T] [LinearOrder L]
    (R : Finset L) (I : L → Finset T) :
    (∑ i ∈ R, ∑ j ∈ R.filter (fun j => i < j), (I i ∩ I j).card) =
      ∑ k ∈ Finset.Icc 2 R.card, ∑ i ∈ R, (orderedTail R I i k).card := by
  calc
    _ = ∑ i ∈ R, ∑ k ∈ Finset.Icc 2 R.card, (orderedTail R I i k).card :=
      Finset.sum_congr rfl fun i hi => ordered_overlap_eq_sum_tails R I hi
    _ = _ := Finset.sum_comm

namespace TubeFamily

variable {T : Type*} [Fintype T] [Nonempty T] {d : ℕ} {A : ℝ≥0} (f : TubeFamily T d A)

/-- The remaining estimate on the sum of the global tails at each large level. -/
noncomputable def GlobalTailSumBound (C : ℝ≥0) : Prop := by
  classical
  exact ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let R := (Finset.univ : Finset Label)
    let I := incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val))
    (∑ k ∈ Finset.Icc 2 R.card, ∑ i ∈ R, ((orderedTail R I i k).card : ℝ)) ≤
      (C : ℝ) * ∑ i ∈ R, ((I i).card : ℝ)

theorem orderedOverlapApplication_of_globalTailSumBound {C : ℝ≥0}
    (h : f.GlobalTailSumBound C) : f.OrderedOverlapApplication C := by
  classical
  intro m hq hr
  let := f.regularOrder m
  let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let R := (Finset.univ : Finset Label)
  let I := incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val))
  let parent := fun i : Label => f.pieces.parent m i.val
  have hp : (R : Set Label).MapsTo parent (f.pieces.B m) := fun i _ => f.pieces.hParent m i.val
  change OrderedOverlapBound C (f.pieces.B m) R parent I
  unfold OrderedOverlapBound
  rw [Finset.sum_fiberwise_of_maps_to hp, Finset.sum_fiberwise_of_maps_to hp]
  have he := congrArg (fun n : ℕ => (n : ℝ)) (global_overlap_eq_sum_tails R I)
  push_cast at he
  exact he.le.trans (h m hq hr)

theorem logarithmic_norm_bound_of_globalTailSumBound (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    {K : ℝ≥0} (h : f.GlobalTailSumBound (tailOverlapConstant d K)) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ :=
  f.logarithmic_norm_bound_of_orderedOverlap hd hN (f.orderedOverlapApplication_of_globalTailSumBound h)

end TubeFamily
end Kakeya.Ninety109
