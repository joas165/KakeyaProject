module

public import Kakeya.Ninety21Theorem46Hall

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Counting retained regular pieces by their selected tube and localization ball. -/
theorem paper_regular_budget_of_tube_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hLarge :
      (8 : ℝ) * (s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1))) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    4 * (paperRegularPieces μ tubes n s.toRetainedDyadicData m).card ≤ Fintype.card T := by
  classical
  let Reg := PaperRegularLabel μ tubes n s.toRetainedDyadicData m
  let Sel := {r : T // r ∈ s.B m}
  let J := Fin (s.ballCount m)
  let hit : Sel → J → Prop :=
    fun r j => (s.ball m j ∩ tubes r.val).Nonempty
  let f : Reg → (Σ r : Sel, {j : J // hit r j}) := by
    intro p
    refine ⟨⟨s.parent m p.val, s.hParent m p.val⟩,
      ⟨s.sourceBall m (Sum.inr p.val), ?_⟩⟩
    obtain ⟨x, hx⟩ := s.hNonempty m (Sum.inr p.val)
    exact ⟨x, s.hSourceBall m (Sum.inr p.val) hx,
      (s.hTrimmed m p.val hx).1⟩
  have hf : Function.Injective f := by
    intro p p' heq
    apply Subtype.ext
    apply hPairInjective
    apply Prod.ext
    · exact congrArg (fun z : (Σ r : Sel, {j : J // hit r j}) => z.1.val) heq
    · exact congrArg (fun z : (Σ r : Sel, {j : J // hit r j}) => z.2.val) heq
  have hCard : Fintype.card Reg ≤
      ∑ r : Sel, Fintype.card {j : J // hit r j} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_le_of_injective f hf)
  have hRealCard : (Fintype.card Reg : ℝ) ≤
      ∑ r : Sel, (Fintype.card {j : J // hit r j} : ℝ) := by
    exact_mod_cast hCard
  have hBall (r : Sel) :
      (Fintype.card {j : J // hit r j} : ℝ) ≤
      s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1)) := by
    have hc : Fintype.card {j : J // hit r j} =
        (Finset.univ.filter (hit r)).card :=
      Fintype.card_subtype (hit r)
    rw [hc]
    simpa [hit, Finset.sum_boole] using s.hHallRight m r.val
  have hCount : (Fintype.card Reg : ℝ) ≤
      ((s.B m).card : ℝ) *
        (s.ballPackingConstant *
          (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
            ((1 : ℝ) / ((n : ℝ) - 1))) := by
    calc
      (Fintype.card Reg : ℝ) ≤
          ∑ r : Sel, (Fintype.card {j : J // hit r j} : ℝ) := hRealCard
      _ ≤ ∑ _r : Sel,
          (s.ballPackingConstant *
            (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
              ((1 : ℝ) / ((n : ℝ) - 1))) := by
            apply Finset.sum_le_sum
            intro r _
            exact hBall r
      _ = ((s.B m).card : ℝ) *
          (s.ballPackingConstant *
            (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
              ((1 : ℝ) / ((n : ℝ) - 1))) := by
            simp [Sel]
  have hb : 0 ≤ ((s.B m).card : ℝ) := Nat.cast_nonneg _
  have hScaled := mul_le_mul_of_nonneg_right hLarge hb
  have hBudgetReal :
      4 * (Fintype.card Reg : ℝ) ≤ (Fintype.card T : ℝ) := by
    nlinarith [s.hGreedy m]
  have hBudgetNat : 4 * Fintype.card Reg ≤ Fintype.card T := by
    exact_mod_cast hBudgetReal
  simpa only [Reg, PaperRegularLabel, Fintype.card_coe] using hBudgetNat

/-- Theorem 4.6 construction data obtained from localized tube–ball counting. -/
noncomputable def paper46Construction_of_tube_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (q : ℕ) (hq : 8 ≤ q)
    (hScale : (q : ℝ) =
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hLarge :
      (8 : ℝ) * (s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1))) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Paper46ConstructionData μ tubes n s.toRetainedDyadicData m :=
  { q := q
    hq := hq
    hScale := hScale
    hRegularBudget :=
      paper_regular_budget_of_tube_ball_count
        μ tubes n s m hPairInjective hLarge }

end Kakeya.Ninety21
