module

public import Kakeya.Ninety21Theorem46Hall

@[expose] public section

open MeasureTheory

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- A quadratic scale threshold controls the tube–ball factor in dimensions n ≥ 3. -/
theorem tube_ball_scale_of_sq_le
    (n : ℕ) (hn : 3 ≤ n) (C q : ℝ) (hC : 0 ≤ C)
    (hq : 1 ≤ q) (hThreshold : (8 * C) ^ 2 ≤ q) :
    8 * (C * q ^ ((1 : ℝ) / ((n : ℝ) - 1))) ≤ q := by
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hExponent : (1 : ℝ) / ((n : ℝ) - 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < (n : ℝ) - 1)).2
    linarith
  have hPower : q ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤ Real.sqrt q := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hq hExponent
  have hRoot : 8 * C ≤ Real.sqrt q := Real.le_sqrt_of_sq_le hThreshold
  calc
    8 * (C * q ^ ((1 : ℝ) / ((n : ℝ) - 1))) ≤
        (8 * C) * Real.sqrt q := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hPower (show 0 ≤ 8 * C by positivity)
    _ ≤ Real.sqrt q * Real.sqrt q :=
      mul_le_mul_of_nonneg_right hRoot (Real.sqrt_nonneg q)
    _ = q := Real.mul_self_sqrt (by linarith)

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

/-- The regular-piece budget at dyadic levels above the quadratic packing threshold. -/
theorem paper_regular_budget_of_sq_le
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) (hn : 3 ≤ n)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hThreshold : (8 * s.ballPackingConstant) ^ 2 ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    4 * (paperRegularPieces μ tubes n s.toRetainedDyadicData m).card ≤
      Fintype.card T := by
  apply paper_regular_budget_of_tube_ball_count μ tubes n s m hPairInjective
  apply tube_ball_scale_of_sq_le n hn _ _ s.hBallPackingConstant _ hThreshold
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

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

/-- Construct Theorem 4.6 data using the natural dyadic scale and tube–ball counting. -/
noncomputable def paper46Construction_of_dyadic_tube_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hq : 8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (hPairInjective : Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hLarge :
      (8 : ℝ) * (s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1))) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Paper46ConstructionData μ tubes n s.toRetainedDyadicData m := by
  have hScale : ((2 ^ m.val : ℕ) : ℝ) =
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m := by
    simp [Kakeya.Eighty4.dyadicScale]
  have hqNat : 8 ≤ (2 ^ m.val : ℕ) := by
    rw [← hScale] at hq
    exact_mod_cast hq
  exact paper46Construction_of_tube_ball_count
    μ tubes n s m (2 ^ m.val) hqNat hScale hPairInjective hLarge

/-- Regular-piece budget for tube–ball pair labels above the packing threshold. -/
theorem paper_regular_budget_of_pair_indexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) (hn : 3 ≤ n)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hThreshold : (8 * s.ballPackingConstant) ^ 2 ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    4 * (paperRegularPieces μ tubes n s.toRetainedDyadicData m).card ≤
      Fintype.card T :=
  paper_regular_budget_of_sq_le μ tubes n hn s m
    (indexing.pair_injective μ tubes n s m) hThreshold

/-- Construct Theorem 4.6 data from tube–ball pair labels and the scale bound. -/
noncomputable def paper46Construction_of_pair_indexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hq : 8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (hLarge :
      (8 : ℝ) * (s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1))) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Paper46ConstructionData μ tubes n s.toRetainedDyadicData m :=
  paper46Construction_of_dyadic_tube_ball_count μ tubes n s m hq
    (indexing.pair_injective μ tubes n s m) hLarge

/-- Analytic cutoff for the Hall construction and the tube–ball packing estimate. -/
def paper46Cutoff (C : ℝ) : ℝ := max 8 ((8 * C) ^ 2)

/-- Theorem 4.6 data for pair-indexed pieces above the analytic cutoff. -/
noncomputable def paper46Construction_of_pair_indexing_at_cutoff
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) (hn : 3 ≤ n)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hq : paper46Cutoff s.ballPackingConstant ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Paper46ConstructionData μ tubes n s.toRetainedDyadicData m := by
  have hEight : 8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m :=
    (le_max_left _ _).trans hq
  have hThreshold : (8 * s.ballPackingConstant) ^ 2 ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m :=
    (le_max_right _ _).trans hq
  exact paper46Construction_of_pair_indexing μ tubes n s indexing m hEight
    (tube_ball_scale_of_sq_le n hn _ _ s.hBallPackingConstant
      (by linarith) hThreshold)

end Kakeya.Ninety21
