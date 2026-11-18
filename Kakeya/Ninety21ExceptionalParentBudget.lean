module

public import Kakeya.Ninety21ExceptionalBudget

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Localization balls supporting exceptional pieces with a fixed selected parent. -/
noncomputable def paperExceptionalParentBallIndices
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) : Finset (Fin (s.ballCount m)) := by
  classical
  exact ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).filter
    (fun p => s.parent m p = r)).image
      (fun p => s.sourceBall m (Sum.inr p))

/-- Pair indexing bounds exceptional pieces by parent-wise ball counts. -/
theorem paper_exceptional_card_le_parent_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hParentBallPacking : ∀ r ∈ s.B m,
      (paperExceptionalParentBallIndices μ tubes n s m r).card ≤ Cexc) :
    (paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card ≤
      Cexc * (s.B m).card := by
  classical
  let Exc := PaperExceptionalLabel μ tubes n s.toRetainedDyadicData m
  let Sel := {r : T // r ∈ s.B m}
  let J := Fin (s.ballCount m)
  let f : Exc →
      (Σ r : Sel,
        {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val}) :=
    fun p =>
      ⟨⟨s.parent m p.val, s.hParent m p.val⟩,
        ⟨s.sourceBall m (Sum.inr p.val), by
          apply Finset.mem_image.mpr
          refine ⟨p.val, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨p.property, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro p p' h
    apply Subtype.ext
    apply hPairInjective
    apply Prod.ext
    · exact congrArg
        (fun z : (Σ r : Sel,
          {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val}) =>
          z.1.val) h
    · exact congrArg
        (fun z : (Σ r : Sel,
          {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val}) =>
          z.2.val) h
  have hCard : Fintype.card Exc ≤
      ∑ r : Sel,
        Fintype.card
          {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val} := by
    simpa only [Fintype.card_sigma] using (Fintype.card_le_of_injective f hf)
  have hEach (r : Sel) :
      Fintype.card
        {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val} ≤
        Cexc := by
    simpa only [Fintype.card_coe] using
      hParentBallPacking r.val r.property
  have hBound : Fintype.card Exc ≤ Fintype.card Sel * Cexc := by
    calc
      Fintype.card Exc ≤
          ∑ r : Sel,
            Fintype.card
              {j : J // j ∈ paperExceptionalParentBallIndices μ tubes n s m r.val} :=
        hCard
      _ ≤ ∑ _r : Sel, Cexc := by
        apply Finset.sum_le_sum
        intro r _
        exact hEach r
      _ = Fintype.card Sel * Cexc := by simp
  have hBound' : Fintype.card Exc ≤ Cexc * Fintype.card Sel := by
    simpa only [Nat.mul_comm] using hBound
  simpa only [Fintype.card_coe, Exc, Sel] using hBound'

/-- Exceptional dyadic budget from parent-wise Vitali-ball packing. -/
theorem paper_exceptional_scaled_budget_of_parent_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hParentBallPacking : ∀ r ∈ s.B m,
      (paperExceptionalParentBallIndices μ tubes n s m r).card ≤ Cexc) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
      2 * (Cexc : ℝ) * (Fintype.card T : ℝ) := by
  let q := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  have hCount := paper_exceptional_card_le_parent_ball_count
    μ tubes n s m Cexc hPairInjective hParentBallPacking
  have hReal :
      ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
        (Cexc : ℝ) * ((s.B m).card : ℝ) := by
    exact_mod_cast hCount
  have hq : 0 ≤ q := le_of_lt (Kakeya.Eighty4.dyadicScale_pos _ m)
  have hC : 0 ≤ (Cexc : ℝ) := Nat.cast_nonneg _
  calc
    q * ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
        q * ((Cexc : ℝ) * ((s.B m).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hReal hq
    _ = (Cexc : ℝ) * (q * ((s.B m).card : ℝ)) := by ring
    _ ≤ (Cexc : ℝ) * (2 * (Fintype.card T : ℝ)) :=
      mul_le_mul_of_nonneg_left (s.hGreedy m) hC
    _ = 2 * (Cexc : ℝ) * (Fintype.card T : ℝ) := by ring

/-- Pair-indexed retained pieces inherit the parent-wise exceptional budget. -/
theorem paper_exceptional_scaled_budget_of_pair_indexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hParentBallPacking : ∀ r ∈ s.B m,
      (paperExceptionalParentBallIndices μ tubes n s m r).card ≤ Cexc) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
      2 * (Cexc : ℝ) * (Fintype.card T : ℝ) :=
  paper_exceptional_scaled_budget_of_parent_ball_count μ tubes n s m Cexc
    (indexing.pair_injective μ tubes n s m) hParentBallPacking

end Kakeya.Ninety21
