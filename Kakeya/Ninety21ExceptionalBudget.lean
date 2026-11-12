module

public import Kakeya.Ninety21RegularBudget

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Localization balls containing an exceptional retained piece. -/
noncomputable def paperExceptionalBallIndices
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Finset (Fin (s.ballCount m)) := by
  classical
  exact (paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).image
    (fun p => s.sourceBall m (Sum.inr p))

/-- Count exceptional pieces by their selected parent and localization ball. -/
theorem paper_exceptional_card_le_tube_ball
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p)))) :
    (paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card ≤
      (s.B m).card * (paperExceptionalBallIndices μ tubes n s m).card := by
  classical
  let Exc := PaperExceptionalLabel μ tubes n s.toRetainedDyadicData m
  let Sel := {r : T // r ∈ s.B m}
  let Balls := {j : Fin (s.ballCount m) //
    j ∈ paperExceptionalBallIndices μ tubes n s m}
  let f : Exc → Sel × Balls := fun p =>
    (⟨s.parent m p.val, s.hParent m p.val⟩,
     ⟨s.sourceBall m (Sum.inr p.val),
       Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩)
  have hf : Function.Injective f := by
    intro p p' h
    apply Subtype.ext
    apply hPairInjective
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst h)
    · exact congrArg Subtype.val (congrArg Prod.snd h)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe,
    Exc, Sel, Balls] using hc

/-- Exceptional-piece count under the exceptional Vitali-ball packing bound. -/
theorem paper_exceptional_card_le_selected
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hExceptionalBallPacking :
      (paperExceptionalBallIndices μ tubes n s m).card ≤ Cexc) :
    (paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card ≤
      Cexc * (s.B m).card := by
  have hCount := paper_exceptional_card_le_tube_ball
    μ tubes n s m hPairInjective
  have hPacked := Nat.mul_le_mul_left (s.B m).card hExceptionalBallPacking
  nlinarith

/-- The exceptional contribution is bounded by a constant multiple of N/q. -/
theorem paper_exceptional_scaled_budget
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hExceptionalBallPacking :
      (paperExceptionalBallIndices μ tubes n s m).card ≤ Cexc) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
      2 * (Cexc : ℝ) * (Fintype.card T : ℝ) := by
  let q := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  have hCount : (paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card ≤
      Cexc * (s.B m).card :=
    paper_exceptional_card_le_selected μ tubes n s m Cexc
      hPairInjective hExceptionalBallPacking
  have hReal : ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
      (Cexc : ℝ) * ((s.B m).card : ℝ) := by
    exact_mod_cast hCount
  have hq : 0 ≤ q := le_of_lt (Kakeya.Eighty4.dyadicScale_pos _ m)
  have hC : 0 ≤ (Cexc : ℝ) := Nat.cast_nonneg _
  calc
    q * ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ) ≤
        q * ((Cexc : ℝ) * ((s.B m).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hReal hq
    _ = (Cexc : ℝ) *
        (q * ((s.B m).card : ℝ)) := by ring
    _ ≤ (Cexc : ℝ) * (2 * (Fintype.card T : ℝ)) :=
      mul_le_mul_of_nonneg_left (s.hGreedy m) hC
    _ = 2 * (Cexc : ℝ) * (Fintype.card T : ℝ) := by ring

/-- Cardinality estimate for the selected and auxiliary labels in Theorem 4.6. -/
theorem paper_selected_exceptional_scaled_budget
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (Cexc : ℕ)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hExceptionalBallPacking :
      (paperExceptionalBallIndices μ tubes n s m).card ≤ Cexc) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((s.B m).card : ℝ) +
        ((paperExceptionalPieces μ tubes n s.toRetainedDyadicData m).card : ℝ)) ≤
      2 * (1 + (Cexc : ℝ)) * (Fintype.card T : ℝ) := by
  have hExc := paper_exceptional_scaled_budget
    μ tubes n s m Cexc hPairInjective hExceptionalBallPacking
  have hGreedy := s.hGreedy m
  nlinarith

end Kakeya.Ninety21
