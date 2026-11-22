module

public import Kakeya.Ninety109FixedParentOverlap
public import Kakeya.Ninety21Theorem46Hall

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal

variable {X T L : Type*} [MeasurableSpace X] [Fintype T]
    {μ : Measure X} {tubes : T → Set X} {d : ℕ}
    {s : RetainedDyadicData (K := L) μ tubes (d + 2)}
    {m : DyadicIndex (Fintype.card T)}

noncomputable abbrev regularLabelOfIndex (a : Paper46ConstructionData μ tubes (d + 2) s m)
    (r : {i // i ∈ paper46RegularIndices μ tubes (d + 2) s m a}) :=
  (paper46RegularIndexEquiv μ tubes (d + 2) s m a).symm r

noncomputable def regularIncidence (a : Paper46ConstructionData μ tubes (d + 2) s m) :=
  incidence tubes (fun r => s.retainedPiece m (Sum.inr (regularLabelOfIndex a r).val))

theorem retained_incidence_lower
    (p : {i : T // i ∈ s.B m} ⊕ {l : L // l ∈ s.P m}) :
    dyadicScale (Fintype.card T) m ≤ ((incidence tubes (s.retainedPiece m) p).card : ℝ) := by
  classical
  obtain ⟨x, hx⟩ := s.hNonempty m p
  have hq := (s.hLevel m p hx).1
  rw [tubeMultiplicity_eq_count] at hq
  have hsub : (Finset.univ.filter fun i => x ∈ tubes i) ⊆
      incidence tubes (s.retainedPiece m) p := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, (Finset.mem_filter.mp hi).2, hx⟩
  exact hq.trans (by exact_mod_cast Finset.card_le_card hsub)

theorem dyadicScale_le_regularIncidence_card (a : Paper46ConstructionData μ tubes (d + 2) s m)
    (r : {i // i ∈ paper46RegularIndices μ tubes (d + 2) s m a}) :
    dyadicScale (Fintype.card T) m ≤ ((regularIncidence a r).card : ℝ) :=
  retained_incidence_lower (Sum.inr (regularLabelOfIndex a r).val)

theorem regular_piece_count_of_lemma48_application [LinearOrder T]
    (a : Paper46ConstructionData μ tubes (d + 2) s m) (C : ℝ≥0)
    (happ : Lemma48Application d C (s.B m) Finset.univ
      (fun r => s.parent m (regularLabelOfIndex a r).val) (regularIncidence a)) :
    let total := ∑ r, ((regularIncidence a r).card : ℝ)
    dyadicScale (Fintype.card T) m * (paperRegularPieces μ tubes (d + 2) s m).card ≤ total ∧
      total ≤ (1 + 2 * dyadicOverlapConstant d C) * Fintype.card T := by
  classical
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ)
      (fun r _ => dyadicScale_le_regularIncidence_card a r)
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe,
      paper46RegularIndices_card, mul_comm] using h
  · exact incidence_sum_of_lemma48_application d C (s.B m) Finset.univ _
      (fun r _ => s.hParent m (regularLabelOfIndex a r).val) (regularIncidence a) happ

theorem regular_label_count_of_ordered_overlap [DecidableEq T]
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] (K : ℝ≥0)
    (happ : OrderedOverlapBound K (s.B m) Finset.univ
      (fun p : PaperRegularLabel μ tubes (d + 2) s m => s.parent m p.val)
      (incidence tubes (fun p => s.retainedPiece m (Sum.inr p.val)))) :
    let I := incidence tubes (fun p : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr p.val))
    let total := ∑ p, ((I p).card : ℝ)
    dyadicScale (Fintype.card T) m * (paperRegularPieces μ tubes (d + 2) s m).card ≤ total ∧
      total ≤ (1 + 2 * (K : ℝ)) * Fintype.card T := by
  classical
  constructor
  · have h := Finset.sum_le_sum (s := Finset.univ)
      (fun (p : PaperRegularLabel μ tubes (d + 2) s m) _ =>
        retained_incidence_lower (s := s) (m := m) (Sum.inr p.val))
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, PaperRegularLabel,
      Fintype.card_coe, incidence, mul_comm] using h
  · exact incidence_sum_of_ordered_overlap K (s.B m) Finset.univ _
      (fun p _ => s.hParent m p.val) _ happ

theorem regular_label_count_of_lemma48_application [DecidableEq T]
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] (C : ℝ≥0)
    (happ : Lemma48Application d C (s.B m) Finset.univ
      (fun p : PaperRegularLabel μ tubes (d + 2) s m => s.parent m p.val)
      (incidence tubes (fun p => s.retainedPiece m (Sum.inr p.val)))) :
    let I := incidence tubes (fun p : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr p.val))
    let total := ∑ p, ((I p).card : ℝ)
    dyadicScale (Fintype.card T) m * (paperRegularPieces μ tubes (d + 2) s m).card ≤ total ∧
      total ≤ (1 + 2 * dyadicOverlapConstant d C) * Fintype.card T := by
  let K : ℝ≥0 := ⟨dyadicOverlapConstant d C, by
    unfold dyadicOverlapConstant overlapConstant
    have : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹ := tsum_nonneg fun _ => by positivity
    positivity⟩
  exact regular_label_count_of_ordered_overlap (s := s) K happ

end Kakeya.Ninety109
