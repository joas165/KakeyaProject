module

public import Kakeya.Ninety110OrderedTails
public import Kakeya.Ninety109ExceptionalCount
public import Kakeya.Ninety109TubeFamily

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal
open Classical

variable {X T L : Type*} [MeasurableSpace X] [Fintype T]
    {μ : Measure X} {tubes : T → Set X} {d : ℕ}

noncomputable def regularApplication (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] : Prop := by
  classical
  exact OrderedTailApplication d K (dyadicScale (Fintype.card T) m)
    (Finset.univ : Finset (PaperRegularLabel μ tubes (d + 2) s m))
    (incidence tubes (fun i : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr i.val)))

noncomputable def regularSelection2 (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] : Prop := by
  classical
  let R := (Finset.univ : Finset (PaperRegularLabel μ tubes (d + 2) s m))
  let I := incidence tubes (fun i : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr i.val))
  exact ∀ i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
    ((Finset.univ.filter (fun ℓ : T =>
      k ≤ (laterPieceIncidences R I i ℓ).card)).card : ℝ) ≤
      (K : ℝ) * dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹

noncomputable def regularTailChain (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] : Prop := by
  classical
  exact OrderedTailChainApplication d K (dyadicScale (Fintype.card T) m)
    (Finset.univ : Finset (PaperRegularLabel μ tubes (d + 2) s m))
    (incidence tubes (fun i : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr i.val)))

theorem regularApplication_of_tail_chain
    (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)]
    (hchain : regularTailChain s K m) : regularApplication s K m := by
  classical
  exact orderedTailApplication_of_tail_chain (d := d) K (dyadicScale (Fintype.card T) m)
    Finset.univ (incidence tubes (fun i : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr i.val))) hchain

theorem regularApplication_of_selection2
    (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)]
    (hselection2 : regularSelection2 s K m) : regularApplication s K m := by
  classical
  exact orderedTailApplication_of_selection2 (d := d) K (dyadicScale (Fintype.card T) m)
    Finset.univ (incidence tubes (fun i : PaperRegularLabel μ tubes (d + 2) s m =>
      s.retainedPiece m (Sum.inr i.val))) hselection2

noncomputable def regularOrderedOverlap (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (C : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] : Prop := by
  classical
  exact OrderedOverlapBound C (s.B m) Finset.univ
    (fun i : PaperRegularLabel μ tubes (d + 2) s m => s.parent m i.val)
    (incidence tubes (fun i => s.retainedPiece m (Sum.inr i.val)))

private theorem complete_count (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (A K : ℝ≥0) (m : DyadicIndex (Fintype.card T))
    [LinearOrder (PaperRegularLabel μ tubes (d + 2) s m)] (ho : regularOrderedOverlap s (tailOverlapConstant d K) m)
    (he : dyadicScale (Fintype.card T) m * (paperExceptionalPieces μ tubes (d + 2) s m).card ≤
      4 * (1 + 2 * dyadicOverlapConstant d A) * Fintype.card T) :
    dyadicScale (Fintype.card T) m * ((s.B m).card + ((s.P m).card : ℝ)) ≤
      (7 + 2 * (tailOverlapConstant d K : ℝ) + 8 * dyadicOverlapConstant d A) * Fintype.card T := by
  classical
  have hr := regular_label_count_of_ordered_overlap (s := s) _ ho
  have hreg := hr.1.trans hr.2
  have hp := paper_regular_exceptional_card μ tubes (d + 2) s m
  have hp' : ((s.P m).card : ℝ) = (paperRegularPieces μ tubes (d + 2) s m).card +
      (paperExceptionalPieces μ tubes (d + 2) s m).card := by exact_mod_cast hp.symm
  rw [hp']
  linarith [s.hGreedy m]

private theorem level_budget [IsFiniteMeasure μ]
    (s : RetainedDyadicData (K := L) μ tubes (d + 2))
    (c : RetainedGreedyAtLevels μ tubes (d + 2) s)
    (hT : ∀ i, MeasurableSet (tubes i)) (D : ℝ) (hD : 0 ≤ D)
    (m : DyadicIndex (Fintype.card T))
    (hc : dyadicScale (Fintype.card T) m * ((s.B m).card + ((s.P m).card : ℝ)) ≤
      D * Fintype.card T) :
    dyadicScale (Fintype.card T) m ^ (1 + (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) *
      Conditional.mass μ (concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * s.C * D * s.Z * s.radiusCap := by
  classical
  let H := (1 : ℝ) / (1 - Real.exp (-1))
  let q := dyadicScale (Fintype.card T) m
  let α := (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
  have hH : 0 ≤ H := div_nonneg zero_le_one
    (by linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)])
  have hq : 0 < q := dyadicScale_pos _ _
  have hV := paper46_retained_capture μ tubes (d + 2) s c hT m
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => s.hVolume m p)
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_sum,
    Fintype.card_coe, Nat.cast_add] at hsum
  have hZ := (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have h1 := hV.trans (mul_le_mul_of_nonneg_left hsum hH)
  change q ^ (1 + α) * _ ≤ H * s.C * D * s.Z * s.radiusCap
  rw [Real.rpow_add hq, Real.rpow_one]
  calc
    _ ≤ q * q ^ α * (H * (((s.B m).card + ((s.P m).card : ℝ)) *
        (s.C * s.deltaPow * s.radius m))) := by gcongr
    _ = (H * s.C * (q ^ α * s.radius m) * s.deltaPow) *
        (q * ((s.B m).card + ((s.P m).card : ℝ))) := by ring
    _ ≤ (H * s.C * (q ^ α * s.radius m) * s.deltaPow) * (D * Fintype.card T) := by
      exact mul_le_mul_of_nonneg_left hc (by
        have := s.hC
        have := s.hRadiusNonneg m
        have := s.hDeltaPow
        positivity)
    _ = H * s.C * D * ((Fintype.card T : ℝ) * s.deltaPow) * (q ^ α * s.radius m) := by ring
    _ ≤ H * s.C * D * s.Z * s.radiusCap := by
      have hcoef := mul_nonneg (mul_nonneg hH s.hC) hD
      exact mul_le_mul (mul_le_mul_of_nonneg_left s.hNormalization hcoef)
        (s.hRadiusScale m) (mul_nonneg (Real.rpow_nonneg hq.le _) (s.hRadiusNonneg m))
        (mul_nonneg hcoef hZ)

namespace TubeFamily

variable [Nonempty T] {A : ℝ≥0} (f : TubeFamily T d A)

noncomputable def supportVolume := volume.restrict (⋃ i, f.tube i)

instance : IsFiniteMeasure f.supportVolume :=
  isFiniteMeasure_restrict.mpr <| IsCompact.measure_lt_top (μ := volume)
    (isCompact_iUnion (fun i => isCompact_unitTube (f.center i) (f.direction i) f.δ)) |>.ne

omit [Nonempty T] in
theorem supportVolume_le : f.supportVolume ≤ volume := Measure.restrict_le_self

noncomputable abbrev pieces := f.retained f.supportVolume f.supportVolume_le

noncomputable abbrev regularOrder (m : DyadicIndex (Fintype.card T)) :
    LinearOrder (PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m) := by
  let g := (f.candidates f.supportVolume).retained
  apply LinearOrder.lift' (fun z => toLex (g.stage m z.val.val.1, z.val.val.2))
  intro x y he
  have hp : g.stage m x.val.val.1 = g.stage m y.val.val.1 :=
    congrArg (fun t => (ofLex t).1) he
  have hx := g.hChosen m _ (g.hPSelected m _ x.val.property)
  have hy := g.hChosen m _ (g.hPSelected m _ y.val.property)
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (hx.symm.trans ((congrArg (g.chosen m) hp).trans hy))
    (congrArg (fun t => (ofLex t).2) he)

theorem regular_label_pair_injective (m : DyadicIndex (Fintype.card T)) :
    Function.Injective
      (fun j : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m =>
        j.val.val) := by
  intro j j' h
  exact Subtype.ext (Subtype.ext h)

theorem regular_parent_forward_hit (m : DyadicIndex (Fintype.card T))
    (c : T)
    (j : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    (ℓ : T) (hj : f.pieces.parent m j.val = c)
    (hℓ : ℓ ∈ incidence f.tube
      (fun r : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m =>
        f.pieces.retainedPiece m (Sum.inr r.val)) j) :
    let v := f.candidates f.supportVolume
    let b := v.retained.ballOf m (Sum.inr j.val)
    b ∈ v.selected m c ∧
      (f.tube ℓ ∩ f.tube c ∩
        Metric.ball (v.centers m b) (3 * v.radius m)).Nonempty := by
  let v := f.candidates f.supportVolume
  let b := v.retained.ballOf m (Sum.inr j.val)
  have hparent : v.retained.tubeOf m (Sum.inr j.val) = c := hj
  have hselected : b ∈ v.selected m c :=
    v.parent_associated_mem_selected m c b ⟨Sum.inr j.val, hparent, rfl⟩
  have hinc : ℓ ∈ incidence f.tube (coverPiece v m) (Sum.inr j.val) := hℓ
  have hhit := triple_hit_of_coverPiece_incidence v m (Sum.inr j.val) ℓ hinc
  rw [hparent] at hhit
  exact ⟨hselected, hhit⟩

open Classical in
theorem regular_hforward_along_parent (m : DyadicIndex (Fintype.card T))
    (c : T)
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m) :
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
    let I := incidence f.tube (fun j : L => f.pieces.retainedPiece m (Sum.inr j.val))
    let v := f.candidates f.supportVolume
    let b := fun j : L => v.retained.ballOf m (Sum.inr j.val)
    ∀ ℓ ∈ I i, ∀ j ∈ laterPieceIncidences R I i ℓ,
      b j ∈ v.selected m c ∧
        (f.tube ℓ ∩ f.tube c ∩
          Metric.ball (v.centers m (b j)) (3 * v.radius m)).Nonempty := by
  classical
  let := f.regularOrder m
  dsimp only
  intro ℓ _ j hj
  have hjR := (Finset.mem_filter.mp hj).1
  have hjparent : f.pieces.parent m j.val = c :=
    (Finset.mem_filter.mp hjR).2
  have hinc : ℓ ∈ incidence f.tube
      (fun r : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m =>
        f.pieces.retainedPiece m (Sum.inr r.val)) j :=
    (Finset.mem_filter.mp hj).2.2
  exact f.regular_parent_forward_hit m c j ℓ hjparent hinc

open Classical in
theorem regular_tail_card_along_parent (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    {k : ℕ} (hk : multipleThreshold d ≤ k) :
    letI := f.regularOrder m
    let R := Finset.univ.filter (fun j : PaperRegularLabel f.supportVolume f.tube (d + 2)
      f.pieces m => f.pieces.parent m j.val = f.pieces.parent m i.val)
    let I := incidence f.tube (fun j : PaperRegularLabel f.supportVolume f.tube (d + 2)
      f.pieces m => f.pieces.retainedPiece m (Sum.inr j.val))
    ((orderedTail R I i k).card : ℝ) ≤
      (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * ((A : ℝ) ^ (d + 1))⁻¹) *
        dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  let := f.regularOrder m
  let v := f.candidates f.supportVolume
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let c := f.pieces.parent m i.val
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L => coverPiece v m (Sum.inr j.val))
  let b := fun j : L => v.retained.ballOf m (Sum.inr j.val)
  have par {j : L} (hj : j ∈ R) : v.retained.tubeOf m (Sum.inr j.val) = c :=
    (Finset.mem_filter.mp hj).2
  have hforward := f.regular_hforward_along_parent m c i
  have hc := ConcreteGreedyVitaliCandidates.retained_parents_subset _ v m (f.pieces.hParent m i.val)
  have ht := fixed_tube_vitali_piece_tail v m c hc f.positive
    (delta_le_canonicalGreedyVitaliRadius_of_total_scale d A f.δ f.positive.le f.scale m)
    f.unit f.separated hk A _ (dyadicScale_pos _ m) (by
      change canonicalGreedyVitaliRadius (T := T) (d + 2) A m = _
      unfold canonicalGreedyVitaliRadius
      congr 2
      push_cast
      ring_nf)
  change ((orderedTail R I i k).card : ℝ) ≤ _
  apply le_trans _ ht
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ℓ hℓ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hℓ).2.trans ?_⟩
  apply Finset.card_le_card_of_injOn b
  · intro j hj
    obtain ⟨hr, _, hlj⟩ := Finset.mem_filter.mp hj
    have hsel := (hforward ℓ (Finset.mem_filter.mp hℓ).1 j hj).1
    exact Finset.mem_filter.mpr ⟨hsel, Sum.inr j.val, par hr, rfl, hlj⟩
  · intro x hx y hy he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((par (Finset.mem_filter.mp hx).1).trans (par (Finset.mem_filter.mp hy).1).symm)
      (congrArg Fin.val he)


open Classical in
theorem regular_parent_incidence_tail (m : DyadicIndex (Fintype.card T))
    (c : T) (hc : c ∈ f.pieces.B m)
    {k : ℕ} (hk : multipleThreshold d ≤ k) :
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
    let I := incidence f.tube (fun j : L =>
      f.pieces.retainedPiece m (Sum.inr j.val))
    ((Finset.univ.filter (fun ℓ : T =>
      k ≤ (R.filter (fun j => ℓ ∈ I j)).card)).card : ℝ) ≤
      (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) *
        ((A : ℝ) ^ (d + 1))⁻¹) *
        dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  let v := f.candidates f.supportVolume
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L => coverPiece v m (Sum.inr j.val))
  let b := fun j : L => v.retained.ballOf m (Sum.inr j.val)
  have par {j : L} (hj : j ∈ R) : v.retained.tubeOf m (Sum.inr j.val) = c :=
    (Finset.mem_filter.mp hj).2
  have hc' := ConcreteGreedyVitaliCandidates.retained_parents_subset _ v m hc
  have ht := fixed_tube_vitali_piece_tail v m c hc' f.positive
    (delta_le_canonicalGreedyVitaliRadius_of_total_scale d A f.δ
      f.positive.le f.scale m)
    f.unit f.separated hk A _ (dyadicScale_pos _ m) (by
      change canonicalGreedyVitaliRadius (T := T) (d + 2) A m = _
      unfold canonicalGreedyVitaliRadius
      congr 2
      push_cast
      ring_nf)
  change ((Finset.univ.filter (fun ℓ : T =>
    k ≤ (R.filter (fun j => ℓ ∈ I j)).card)).card : ℝ) ≤ _
  apply le_trans _ ht
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ℓ hℓ
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hℓ).2.trans ?_⟩
  apply Finset.card_le_card_of_injOn b
  · intro j hj
    obtain ⟨hr, hlj⟩ := Finset.mem_filter.mp hj
    have hsel := v.parent_associated_mem_selected m c (b j)
      ⟨Sum.inr j.val, par hr, rfl⟩
    exact Finset.mem_filter.mpr ⟨hsel, Sum.inr j.val, par hr, rfl, hlj⟩
  · intro x hx y hy he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext
      ((par (Finset.mem_filter.mp hx).1).trans
        (par (Finset.mem_filter.mp hy).1).symm)
      (congrArg Fin.val he)

noncomputable def fixedParentTailConstant (d : ℕ) (A : ℝ≥0) : ℝ≥0 :=
  ⟨2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) *
    ((A : ℝ) ^ (d + 1))⁻¹, by positivity⟩

noncomputable def globalVitaliBalls
    (m : DyadicIndex (Fintype.card T)) :=
  let v := f.candidates f.supportVolume
  Finset.univ.image fun p : CoverLabel v m => v.retained.ballOf m p

theorem retainedPiece_subset_global_vitali_ball
    (m : DyadicIndex (Fintype.card T)) (p : CoverLabel (f.candidates f.supportVolume) m) :
    let v := f.candidates f.supportVolume
    let b := v.retained.ballOf m p
    b ∈ f.globalVitaliBalls m ∧
      f.pieces.retainedPiece m p ⊆ Metric.ball (v.centers m b) (3 * v.radius m) := by
  exact ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, fun _ hx => hx.2⟩

def GlobalVitaliDisjoint : Prop :=
  ∀ m : DyadicIndex (Fintype.card T),
    let v := f.candidates f.supportVolume
    ∀ r ∈ f.globalVitaliBalls m, ∀ s ∈ f.globalVitaliBalls m,
      r ≠ s →
        Disjoint (Metric.ball (v.centers m r) (v.radius m))
          (Metric.ball (v.centers m s) (v.radius m))

noncomputable def fixedParentTubeTail
    (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    (k : ℕ) : Finset T := by
  classical
  let v := f.candidates f.supportVolume
  let c := f.pieces.parent m i.val
  exact Finset.univ.filter fun ℓ : T =>
    k ≤ ((f.globalVitaliBalls m).filter fun b =>
      (f.tube ℓ ∩ f.tube c ∩
        Metric.ball (v.centers m b) (3 * v.radius m)).Nonempty).card

open Classical in
theorem fixed_parent_tube_tail_card
    (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    (hballs : f.GlobalVitaliDisjoint)
    {k : ℕ} (hk : multipleThreshold d ≤ k) :
    ((f.fixedParentTubeTail m i k).card : ℝ) ≤
      (fixedParentTailConstant d A : ℝ) *
        dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  let v := f.candidates f.supportVolume
  let c := f.pieces.parent m i.val
  have ht := fixed_tube_vitali_ball_tail
    f.center f.direction c f.δ (v.radius m) f.positive
    (delta_le_canonicalGreedyVitaliRadius_of_total_scale
      d A f.δ f.positive.le f.scale m)
    f.unit f.separated (f.globalVitaliBalls m) (v.centers m)
    (hballs m)
    hk A _ (dyadicScale_pos _ m) (by
      change canonicalGreedyVitaliRadius (T := T) (d + 2) A m = _
      unfold canonicalGreedyVitaliRadius
      congr 2
      push_cast
      ring_nf)
  change ((f.fixedParentTubeTail m i k).card : ℝ) ≤ _ at ht
  exact ht

open Classical in
theorem R_c_orderedTail_subset_of_global_vitali_balls
    (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    (k : ℕ) :
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let c := f.pieces.parent m i.val
    let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
    let I := incidence f.tube (fun j : L => f.pieces.retainedPiece m (Sum.inr j.val))
    orderedTail R I i k ⊆ f.fixedParentTubeTail m i k := by
  let := f.regularOrder m
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let c := f.pieces.parent m i.val
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L => f.pieces.retainedPiece m (Sum.inr j.val))
  let v := f.candidates f.supportVolume
  let b := fun j : L => v.retained.ballOf m (Sum.inr j.val)
  dsimp only
  intro ℓ hℓ
  obtain ⟨_, hk_le⟩ := Finset.mem_filter.mp hℓ
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hk_le.trans ?_⟩
  refine Finset.card_le_card_of_injOn b ?_ ?_
  · intro j hj
    obtain ⟨hjR, _, hℓj⟩ := Finset.mem_filter.mp hj
    have hj_par : f.pieces.parent m j.val = c :=
      (Finset.mem_filter.mp hjR).2
    obtain ⟨_, hhit⟩ := f.regular_parent_forward_hit m c j ℓ hj_par hℓj
    have hmem_global : b j ∈ f.globalVitaliBalls m :=
      (f.retainedPiece_subset_global_vitali_ball m (Sum.inr j.val)).1
    exact Finset.mem_filter.mpr ⟨hmem_global, hhit⟩
  · intro x hx y hy hxy
    have hx_par : f.pieces.parent m x.val = c :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    have hy_par : f.pieces.parent m y.val = c :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (hx_par.trans hy_par.symm) (congrArg Fin.val hxy)

noncomputable def ParentSubsetApplication : Prop := by
  classical
  exact ∀ m : DyadicIndex (Fintype.card T),
    8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    ∀ (i : L) (k : ℕ), multipleThreshold d ≤ k →
      let c := f.pieces.parent m i.val
      let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
      let I := incidence f.tube (fun j : L => f.pieces.retainedPiece m (Sum.inr j.val))
      orderedTail R I i k ⊆ f.fixedParentTubeTail m i k

open Classical in
theorem regular_tail_card_of_parent_subset_inclusion
    (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m)
    (hballs : f.GlobalVitaliDisjoint)
    {k : ℕ} (hk : multipleThreshold d ≤ k)
    (hsubset :
      letI := f.regularOrder m
      let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
      let c := f.pieces.parent m i.val
      let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
      let I := incidence f.tube (fun j : L =>
        f.pieces.retainedPiece m (Sum.inr j.val))
      orderedTail R I i k ⊆ f.fixedParentTubeTail m i k) :
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let c := f.pieces.parent m i.val
    let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
    let I := incidence f.tube (fun j : L =>
      f.pieces.retainedPiece m (Sum.inr j.val))
    ((orderedTail R I i k).card : ℝ) ≤
      (fixedParentTailConstant d A : ℝ) *
        dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  let := f.regularOrder m
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let c := f.pieces.parent m i.val
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L =>
    f.pieces.retainedPiece m (Sum.inr j.val))
  have ht := f.fixed_parent_tube_tail_card m i hballs hk
  have hle : ((orderedTail R I i k).card : ℝ) ≤ ((f.fixedParentTubeTail m i k).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hle.trans ht

open Classical in
theorem parentTailApplication_of_parent_subset
    (hballs : f.GlobalVitaliDisjoint)
    (m : DyadicIndex (Fintype.card T))
    (hq8 : 8 ≤ dyadicScale (Fintype.card T) m)
    (hR1 : (f.candidates f.supportVolume).radius m ≤ 1)
    (hsubset : f.ParentSubsetApplication) :
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    ∀ i : L,
      let c := f.pieces.parent m i.val
      let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
      let I := incidence f.tube (fun j : L =>
        f.pieces.retainedPiece m (Sum.inr j.val))
      OrderedTailApplication d (fixedParentTailConstant d A)
        (dyadicScale (Fintype.card T) m) R I := by
  let := f.regularOrder m
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  dsimp only
  intro i
  let c := f.pieces.parent m i.val
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L =>
    f.pieces.retainedPiece m (Sum.inr j.val))
  intro j hj k hk
  have hp : f.pieces.parent m j.val = c := (Finset.mem_filter.mp hj).2
  have h := f.regular_tail_card_of_parent_subset_inclusion m j hballs hk
    (hsubset m hq8 hR1 j k hk)
  simpa only [hp] using h

open Classical in
theorem parentTailApplication_of_ball_map
    (hballs : f.GlobalVitaliDisjoint)
    (m : DyadicIndex (Fintype.card T))
    (i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m) :
    letI := f.regularOrder m
    let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
    let c := f.pieces.parent m i.val
    let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
    let I := incidence f.tube (fun j : L =>
      f.pieces.retainedPiece m (Sum.inr j.val))
    ∀ _hi : i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
      ((orderedTail R I i k).card : ℝ) ≤
        (fixedParentTailConstant d A : ℝ) *
          dyadicScale (Fintype.card T) m * ((k : ℝ) ^ (d + 1))⁻¹ := by
  let := f.regularOrder m
  let L := PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m
  let c := f.pieces.parent m i.val
  let R := Finset.univ.filter (fun j : L => f.pieces.parent m j.val = c)
  let I := incidence f.tube (fun j : L =>
    f.pieces.retainedPiece m (Sum.inr j.val))
  dsimp only
  intro _ k hk
  exact f.regular_tail_card_of_parent_subset_inclusion m i hballs hk
    (f.R_c_orderedTail_subset_of_global_vitali_balls m i k)

def OverlapApplication (K : ℝ≥0) : Prop :=
  ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    regularApplication f.pieces K m

def OrderedOverlapApplication (C : ℝ≥0) : Prop :=
  ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    regularOrderedOverlap f.pieces C m

theorem orderedOverlapApplication_of_tails (hd : 1 ≤ d) {K : ℝ≥0}
    (h : f.OverlapApplication K) : f.OrderedOverlapApplication (tailOverlapConstant d K) := by
  classical
  intro m hq hr
  let := f.regularOrder m
  exact ordered_overlap_of_tails hd K _ (f.pieces.B m) Finset.univ
    (fun i : PaperRegularLabel f.supportVolume f.tube (d + 2) f.pieces m =>
      f.pieces.parent m i.val) _
    (fun i _ => retained_incidence_lower (s := f.pieces) (m := m) (Sum.inr i.val))
    (h m hq hr)

def Selection2Application (K : ℝ≥0) : Prop :=
  ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    regularSelection2 f.pieces K m

def TailChainApplication (K : ℝ≥0) : Prop :=
  ∀ m, 8 ≤ dyadicScale (Fintype.card T) m →
    (f.candidates f.supportVolume).radius m ≤ 1 →
    letI := f.regularOrder m
    regularTailChain f.pieces K m

theorem overlapApplication_of_tail_chain (K : ℝ≥0)
    (hchain : f.TailChainApplication K) : f.OverlapApplication K := by
  intro m hq8 hR1
  let := f.regularOrder m
  exact regularApplication_of_tail_chain f.pieces K m (hchain m hq8 hR1)

theorem overlapApplication_of_selection2 (K : ℝ≥0)
    (hselection2 : f.Selection2Application K) : f.OverlapApplication K := by
  intro m hq8 hR1
  let := f.regularOrder m
  exact regularApplication_of_selection2 f.pieces K m (hselection2 m hq8 hR1)

noncomputable def largeLevelConstant (d : ℕ) (A K : ℝ≥0) : ℝ :=
  (1 / (1 - Real.exp (-1))) * volumeCoefficient d *
    (7 + 2 * (tailOverlapConstant d K : ℝ) + 8 * dyadicOverlapConstant d A) * (A : ℝ) ^ (d + 1) * A

set_option maxHeartbeats 1000000 in
open Classical in
private theorem large_level_bound (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OrderedOverlapApplication (tailOverlapConstant d K))
    (m : DyadicIndex (Fintype.card T)) (hq8 : 8 ≤ dyadicScale (Fintype.card T) m)
    (hR1 : (f.candidates f.supportVolume).radius m ≤ 1) :
    dyadicScale (Fintype.card T) m ^ (1 + (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) *
      Conditional.mass f.supportVolume (concreteDyadicBand f.tube m) ≤ largeLevelConstant d A K := by
  let v := f.candidates f.supportVolume
  let := f.regularOrder m
  have hR : f.δ ≤ v.radius m := by
    change f.δ ≤ canonicalGreedyVitaliRadius (d + 2) (A : ℝ) m
    exact delta_le_canonicalGreedyVitaliRadius_of_total_scale
      d A f.δ f.positive.le f.scale m
  have he := exceptional_cover_count v f.supportVolume (f.bounds _ f.supportVolume_le)
    (f.piece_volume _ f.supportVolume_le) hd A f.positive f.unit f.separated m hR hR1 (by
      change canonicalGreedyVitaliRadius (T := T) (d + 2) A m = _
      unfold canonicalGreedyVitaliRadius
      congr 2
      push_cast
      ring_nf)
  have hc := complete_count f.pieces A K m (happ m hq8 hR1) he
  have hK : 0 ≤ dyadicOverlapConstant d A := by
    unfold dyadicOverlapConstant overlapConstant
    have hseries : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹ := tsum_nonneg fun _ => by positivity
    positivity
  have hc' :
      dyadicScale (Fintype.card T) m *
        (((f.retained f.supportVolume f.supportVolume_le).B m).card +
          (((f.retained f.supportVolume f.supportVolume_le).P m).card : ℝ)) ≤
        (7 + 2 * (tailOverlapConstant d K : ℝ) +
          8 * dyadicOverlapConstant d A) * Fintype.card T := by
    simpa only [TubeFamily.pieces] using hc
  have hlevel :=
    level_budget (f.retained f.supportVolume f.supportVolume_le)
      (f.greedy f.supportVolume f.supportVolume_le) f.measurable
      _ (by positivity) m hc'
  have hC :
      (f.retained f.supportVolume f.supportVolume_le).C =
        volumeCoefficient d := by
    rfl
  have hZ :
      (f.retained f.supportVolume f.supportVolume_le).Z =
        (A : ℝ) ^ (d + 1) := by
    rfl
  have hRadiusCap :
      (f.retained f.supportVolume f.supportVolume_le).radiusCap =
        (A : ℝ) := by
    rfl
  rw [hC, hZ, hRadiusCap] at hlevel
  simpa only [largeLevelConstant] using hlevel

private theorem support_mass_le :
    Conditional.mass f.supportVolume Set.univ ≤
      2 * (1 + A) * tripleRadiusTransverseCoefficient d * (A : ℝ) ^ (d + 1) := by
  classical
  let R : ℝ := 1 + A
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hδA : f.δ ≤ A := by
    have hN : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos (α := T)
    have ha : 0 ≤ (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1) := by
      apply div_nonneg zero_le_one
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
    exact (le_mul_of_one_le_right f.positive.le (Real.one_le_rpow hN ha)).trans f.scale
  have ht (i : T) : f.supportVolume.real (f.tube i) ≤
      2 * R * tripleRadiusTransverseCoefficient d * f.δ ^ (d + 1) := by
    have hs : f.tube i ⊆ Metric.closedBall (f.center i) R := by
      rintro _ ⟨t, w, ht, _, hw, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : f.center i + t • f.direction i + w - f.center i = t • f.direction i + w := by abel
      rw [he]
      have h := norm_add_le (t • f.direction i) w
      rw [norm_smul, f.unit, mul_one, Real.norm_eq_abs] at h
      dsimp [R]; linarith
    have h := TubeBall.unitTube_ball_volume_le_explicit_arbitrary_direction d
      (f.center i) (f.direction i) (f.center i) f.δ R
      (fun he => by simpa [he] using f.unit i) hR
    change volume (f.tube i ∩ Metric.closedBall (f.center i) R) ≤ _ at h
    rw [Set.inter_eq_left.mpr hs] at h
    have hh := ENNReal.toReal_mono (by finiteness) ((f.supportVolume_le (f.tube i)).trans h)
    simp only [ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR),
      ENNReal.toReal_ofReal f.positive.le] at hh
    exact hh.trans_eq (by unfold tripleRadiusTransverseCoefficient; ring)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ht i)
  have hu := (measureReal_iUnion_fintype_le (μ := f.supportVolume) f.tube).trans hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hu
  have hmass : Conditional.mass f.supportVolume Set.univ =
      f.supportVolume.real (⋃ i, f.tube i) := by
    rw [conditional_mass_eq_measure_toReal f.supportVolume _ MeasurableSet.univ]
    simp [supportVolume,
      Measure.real, MeasurableSet.iUnion f.measurable]
  rw [hmass]
  apply hu.trans
  have hw : 0 ≤ tripleRadiusTransverseCoefficient d := ENNReal.toReal_nonneg
  have h := mul_le_mul_of_nonneg_left f.normalization
    (show 0 ≤ 2 * R * tripleRadiusTransverseCoefficient d by positivity)
  dsimp only [R] at *
  linarith

noncomputable def levelConstant (d : ℕ) (A K : ℝ≥0) : ℝ :=
  max (largeLevelConstant d A K)
    ((8 + (A : ℝ) ^ (d + 1)) ^ (1 + (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) *
      (2 * (1 + A) * tripleRadiusTransverseCoefficient d * (A : ℝ) ^ (d + 1)))

open Classical in
theorem level_bound_of_orderedOverlap (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OrderedOverlapApplication (tailOverlapConstant d K))
    (m : DyadicIndex (Fintype.card T)) :
    dyadicScale (Fintype.card T) m ^ (1 + (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) *
      Conditional.mass f.supportVolume (concreteDyadicBand f.tube m) ≤ levelConstant d A K := by
  classical
  let q := dyadicScale (Fintype.card T) m
  have hq := dyadicScale_pos (Fintype.card T) m
  have hden : 0 < (((d + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
  by_cases h : 8 + (A : ℝ) ^ (d + 1) ≤ q
  · have hR : (f.candidates f.supportVolume).radius m ≤ 1 := by
      change (A : ℝ) * q ^ (-((1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1))) ≤ 1
      rw [Real.rpow_neg hq.le, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hq _)]
      have hex : (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1) = (((d + 1 : ℕ) : ℝ))⁻¹ := by push_cast; ring_nf
      rw [hex, ← Real.pow_rpow_inv_natCast A.coe_nonneg (Nat.succ_ne_zero d)]
      have hAq : (A : ℝ) ^ (d + 1) ≤ q := by linarith
      exact Real.rpow_le_rpow (by positivity) hAq (by positivity)
    have h8 : 8 ≤ q := by linarith [pow_nonneg A.coe_nonneg (d + 1)]
    exact (f.large_level_bound hd happ m h8 hR).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (paper46_small_level_budget f.supportVolume f.tube _
      (div_nonneg zero_le_one hden.le) f.measurable m _ (lt_of_not_ge h)).trans
    exact mul_le_mul_of_nonneg_left f.support_mass_le (by positivity)

open Classical in
theorem level_bound (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OverlapApplication K)
    (m : DyadicIndex (Fintype.card T)) :
    dyadicScale (Fintype.card T) m ^ (1 + (1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) *
      Conditional.mass f.supportVolume (concreteDyadicBand f.tube m) ≤ levelConstant d A K := by
  exact f.level_bound_of_orderedOverlap hd (f.orderedOverlapApplication_of_tails hd happ) m

theorem moment_bound_of_orderedOverlap (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OrderedOverlapApplication (tailOverlapConstant d K)) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ≤
      2 ^ p * levelConstant d A K * ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
  have hden : 0 < (((d + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hp : p ≠ 0 := (div_pos (by positivity) hden).ne'
  have h := Eighty9.logarithmic_moment_from_level_budgets f.supportVolume f.tube
    ((1 : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)) (levelConstant d A K)
    (div_nonneg zero_le_one hden.le) f.measurable (f.level_bound_of_orderedOverlap hd happ)
  rw [(Conditional.dimension_exponents (d + 2) (by omega)).1] at h
  have hs : ∀ x, x ∉ ⋃ i, f.tube i → tubeMultiplicity f.tube x ^ p = 0 := by
    intro x hx
    have hnone : ∀ i, x ∉ f.tube i := by simpa using hx
    simp [tubeMultiplicity_eq_count, finiteTubeCount, hnone, Real.zero_rpow hp]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hs).symm.le.trans h

theorem moment_bound (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OverlapApplication K) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ≤
      2 ^ p * levelConstant d A K * ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  exact f.moment_bound_of_orderedOverlap hd (f.orderedOverlapApplication_of_tails hd happ)

theorem norm_bound_of_orderedOverlap (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OrderedOverlapApplication (tailOverlapConstant d K)) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^ p⁻¹ := by
  have hden : 0 < (((d + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
  exact Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (tubeMultiplicity_nonneg _ _) _)
    (f.moment_bound_of_orderedOverlap hd happ) (inv_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hden.le))

theorem norm_bound (hd : 1 ≤ d) {K : ℝ≥0} (happ : f.OverlapApplication K) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^ p⁻¹ := by
  exact f.norm_bound_of_orderedOverlap hd (f.orderedOverlapApplication_of_tails hd happ)

theorem logarithmic_norm_bound_of_orderedOverlap (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    {K : ℝ≥0} (happ : f.OrderedOverlapApplication (tailOverlapConstant d K)) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ := by
  let N := Fintype.card T
  let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hpowers : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N ≠ 0 by dsimp [N]; omega)
  have hfloor := Real.log_le_log (by positivity) hpowers
  rw [Real.log_pow] at hfloor
  have hlevels : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ (2 / Real.log 2) * Real.log N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]
    push_cast
    linarith
  have hC : 0 ≤ levelConstant d A K := by
    apply le_trans _ (le_max_right _ _)
    have hω : 0 ≤ tripleRadiusTransverseCoefficient d := ENNReal.toReal_nonneg
    positivity
  have hbase : 0 ≤ (2 : ℝ) ^ p * levelConstant d A K := by positivity
  have hn : 0 < (((d + 2 : ℕ) : ℝ) - 1) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hpow : 0 ≤ p⁻¹ := inv_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hn.le)
  apply (f.norm_bound_of_orderedOverlap hd happ).trans
  change _ ≤ ((2:ℝ) ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ * (Real.log N) ^ p⁻¹
  rw [← Real.mul_rpow (by positivity) (Real.log_natCast_nonneg N)]
  apply Real.rpow_le_rpow (by positivity) _ hpow
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlevels hbase


theorem logarithmic_norm_bound (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    {K : ℝ≥0} (happ : f.OverlapApplication K) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ := by
  exact f.logarithmic_norm_bound_of_orderedOverlap hd hN (f.orderedOverlapApplication_of_tails hd happ)
theorem logarithmic_norm_bound_of_tail_chain (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    {K : ℝ≥0} (hchain : f.TailChainApplication K) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ := by
  exact f.logarithmic_norm_bound hd hN (f.overlapApplication_of_tail_chain K hchain)

theorem logarithmic_norm_bound_of_selection2 (hd : 1 ≤ d) (hN : 2 ≤ Fintype.card T)
    {K : ℝ≥0} (hselection2 : f.Selection2Application K) :
    let p := ((d + 2 : ℕ) : ℝ) / (((d + 2 : ℕ) : ℝ) - 1)
    (∫ x, tubeMultiplicity f.tube x ^ p) ^ p⁻¹ ≤
      (2 ^ p * levelConstant d A K * (2 / Real.log 2)) ^ p⁻¹ *
        (Real.log (Fintype.card T)) ^ p⁻¹ := by
  exact f.logarithmic_norm_bound hd hN (f.overlapApplication_of_selection2 K hselection2)

end TubeFamily
end Kakeya.Ninety109
