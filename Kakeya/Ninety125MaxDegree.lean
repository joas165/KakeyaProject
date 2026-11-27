module

public import Kakeya.Ninety118FirstEquality

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal

section

variable {T L : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
variable (R : Finset L) (I : L → Finset T) (parent : L → T)

/-- All retained labels incident to an original tube. -/
def incidentLabels (ℓ : T) : Finset L := R.filter fun i => ℓ ∈ I i

/-- The maximum of the parent degrees over all original tubes (page 16). -/
noncomputable def maxParentDegree (ℓ : T) : ℕ :=
  (Finset.univ.image fun c : T => ((incidentLabels R I ℓ).filter
    fun j => parent j = c).card).max' (Finset.univ_nonempty.image _)

theorem maxParentDegree_le_globalDegree (ℓ : T) :
    maxParentDegree R I parent ℓ ≤ (incidentLabels R I ℓ).card := by
  classical
  let S := incidentLabels R I ℓ
  let degree := fun c : T => (S.filter fun j => parent j = c).card
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp
    ((Finset.univ.image degree).max'_mem (Finset.univ_nonempty.image _))
  change (Finset.univ.image degree).max' _ ≤ S.card
  rw [← hc]
  exact Finset.card_le_card (Finset.filter_subset _ S)

/-- Page 16 splits the global threshold into the maximizing-parent term and the remainder. -/
theorem degree_threshold_card_split (i : L) (k : ℕ) :
    ((I i).filter fun ℓ => k ≤ (incidentLabels R I ℓ).card).card =
      ((I i).filter fun ℓ => k ≤ maxParentDegree R I parent ℓ).card +
      ((I i).filter fun ℓ => maxParentDegree R I parent ℓ < k ∧
        k ≤ (incidentLabels R I ℓ).card).card := by
  let S := (I i).filter fun ℓ => k ≤ (incidentLabels R I ℓ).card
  have h₁ : S.filter (fun ℓ => k ≤ maxParentDegree R I parent ℓ) =
      (I i).filter (fun ℓ => k ≤ maxParentDegree R I parent ℓ) := by
    ext ℓ
    simp only [S, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, h.2.trans (maxParentDegree_le_globalDegree R I parent ℓ)⟩, h.2⟩⟩
  have h₂ : S.filter (fun ℓ => ¬ k ≤ maxParentDegree R I parent ℓ) =
      (I i).filter (fun ℓ => maxParentDegree R I parent ℓ < k ∧
        k ≤ (incidentLabels R I ℓ).card) := by
    ext ℓ
    simp only [S, Finset.mem_filter, not_le]
    tauto
  rw [← h₁, ← h₂]
  exact (Finset.card_filter_add_card_filter_not _).symm

/-- The conditional step in the manuscript. -/
def MaxDegreeDominates : Prop :=
  ∀ ℓ, (incidentLabels R I ℓ).card ≤ maxParentDegree R I parent ℓ

/-- At every threshold the remainder on page 16 is empty. -/
theorem degree_remainder_eq_empty (h : MaxDegreeDominates R I parent) (i : L) (k : ℕ) :
    ((I i).filter fun ℓ => maxParentDegree R I parent ℓ < k ∧
      k ≤ (incidentLabels R I ℓ).card) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ℓ hℓ
  obtain ⟨_, hlt, hle⟩ := Finset.mem_filter.mp hℓ
  exact (Nat.not_lt_of_ge (hle.trans (h ℓ))) hlt

/-- The two threshold sets in equation (9) agree. -/
theorem degree_threshold_eq_of_maxDegree (h : MaxDegreeDominates R I parent)
    (i : L) (k : ℕ) :
    ((I i).filter fun ℓ => k ≤ (incidentLabels R I ℓ).card) =
      (I i).filter fun ℓ => k ≤ maxParentDegree R I parent ℓ := by
  ext ℓ
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ =>
    ⟨fun hk => hk.trans (h ℓ), fun hk => hk.trans (maxParentDegree_le_globalDegree R I parent ℓ)⟩

/-- A maximizing parent contains the entire incident label set under dominance. -/
theorem parent_eq_of_maxDegree (h : MaxDegreeDominates R I parent)
    {ℓ : T} {i j : L} (hi : i ∈ incidentLabels R I ℓ) (hj : j ∈ incidentLabels R I ℓ) :
    parent j = parent i := by
  classical
  let S := incidentLabels R I ℓ
  let degree := fun c : T => (S.filter fun r => parent r = c).card
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp
    ((Finset.univ.image degree).max'_mem (Finset.univ_nonempty.image _))
  have hall : S.filter (fun r => parent r = c) = S := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    exact (h ℓ).trans hc.ge
  have hp {r : L} (hr : r ∈ S) : parent r = c :=
    (Finset.mem_filter.mp (hall.symm ▸ hr : r ∈ S.filter (fun s => parent s = c))).2
  exact (hp hj).trans (hp hi).symm

variable [LinearOrder L]

private theorem sum_threshold_weights (n : ℕ) :
    (∑ k ∈ Finset.Icc 2 n, (k - 1)) = n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ (n + 1) 1]
      simp [Nat.add_comm]

omit [Nonempty T] in
/-- The weighted global multiplicity identity in Lemma 4.9 and equation (8). -/
theorem orderedTail_sum_eq_weighted_degrees :
    (∑ k ∈ Finset.Icc 2 R.card, ∑ i ∈ R, (orderedTail R I i k).card) =
      ∑ k ∈ Finset.Icc 2 R.card, (k - 1) *
        (Finset.univ.filter fun ℓ : T => k ≤ (incidentLabels R I ℓ).card).card := by
  classical
  let pairs := (R ×ˢ R).filter fun ij => ij.1 < ij.2
  have left : (∑ i ∈ R, ∑ j ∈ R.filter (fun j => i < j), (I i ∩ I j).card) =
      ∑ ij ∈ pairs, (I ij.1 ∩ I ij.2).card := by
    simp [pairs, Finset.sum_filter, Finset.sum_product]
  have inter (ij : L × L) : I ij.1 ∩ I ij.2 =
      Finset.univ.filter (fun ℓ => ℓ ∈ I ij.1 ∧ ℓ ∈ I ij.2) := by ext; simp
  have count (ℓ : T) : pairs.filter (fun ij => ℓ ∈ I ij.1 ∧ ℓ ∈ I ij.2) =
      ((incidentLabels R I ℓ) ×ˢ (incidentLabels R I ℓ)).filter (fun ij => ij.1 < ij.2) := by
    ext
    simp [pairs, incidentLabels]
    tauto
  rw [← global_overlap_eq_sum_tails, left]
  simp_rw [inter, Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.Icc 2 R.card)]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [← Finset.card_filter, count, Finset.card_product_filter_lt, ← sum_threshold_weights]
  let D := (incidentLabels R I ℓ).card
  have hd : D ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
  have lev : (Finset.Icc 2 R.card).filter (fun k => k ≤ D) = Finset.Icc 2 D := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  change (∑ k ∈ Finset.Icc 2 D, (k - 1)) =
    ∑ k ∈ Finset.Icc 2 R.card, (k - 1) * (if k ≤ D then 1 else 0)
  rw [← lev, Finset.sum_filter]
  simp [mul_ite]

theorem orderedTail_eq_of_maxDegree (h : MaxDegreeDominates R I parent)
    {i : L} (hi : i ∈ R) (k : ℕ) :
    orderedTail R I i k = orderedTail (R.filter fun j => parent j = parent i) I i k := by
  classical
  unfold orderedTail
  apply Finset.ext
  intro ℓ
  by_cases hℓ : ℓ ∈ I i
  · have he : (R.filter fun j => i ≤ j ∧ ℓ ∈ I j) =
        ((R.filter fun j => parent j = parent i).filter fun j => i ≤ j ∧ ℓ ∈ I j) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hij, hjℓ⟩
        exact ⟨⟨hj, parent_eq_of_maxDegree R I parent h (Finset.mem_filter.mpr ⟨hi, hℓ⟩)
          (Finset.mem_filter.mpr ⟨hj, hjℓ⟩)⟩, hij, hjℓ⟩
      · rintro ⟨⟨hj, _⟩, hij, hjℓ⟩
        exact ⟨hj, hij, hjℓ⟩
    simp only [Finset.mem_filter, he]
  · simp [hℓ]

end

namespace TubeFamily

variable {T : Type*} [Fintype T] [Nonempty T] {d : ℕ} {A : ℝ≥0} (f : TubeFamily T d A)

noncomputable def MaxDegreeApplication : Prop := by
  classical
  exact ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    MaxDegreeDominates (Finset.univ : Finset Label)
      (incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val)))
      (fun i : Label => f.pieces.parent m i.val)

theorem overlapApplication_of_maxDegree (h : f.MaxDegreeApplication) :
    f.OverlapApplication (fixedParentTailConstant d A) := by
  classical
  intro m hq hr
  let := f.regularOrder m
  let Label := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let I := incidence f.tube (fun i : Label => f.pieces.retainedPiece m (Sum.inr i.val))
  let parent := fun i : Label => f.pieces.parent m i.val
  intro i hi k hk
  change ((orderedTail Finset.univ I i k).card : ℝ) ≤ _
  rw [orderedTail_eq_of_maxDegree Finset.univ I parent (h m hq hr) hi k]
  exact f.regular_tail_card_along_parent m i hk

theorem logarithmic_norm_bound_of_maxDegree (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    (h : f.MaxDegreeApplication) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A (fixedParentTailConstant d A) * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ :=
  f.logarithmic_norm_bound hd hN (f.overlapApplication_of_maxDegree h)

end TubeFamily
end Kakeya.Ninety109
