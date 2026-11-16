module

public import Kakeya.Ninety21VitaliIndexBudget
public import Kakeya.Ninety21Theorem46Endpoint

/-!
# Two-radius Vitali analytic endpoint

The radius-R balls index the selected Vitali subfamily and enter the retained
cardinality estimate. Their radius-3R enlargements cover the greedy union.
The endpoint uses the enlarged tube-ball mass directly, without asserting
coverage by the smaller retained pieces.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- Finite subadditivity of real mass for a doubly indexed cover. -/
theorem twoRadius_mass_le_double_sum
    {X T I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (B : Finset T) (S : T → Finset I)
    (U : Set X) (E : T → I → Set X)
    (hU : MeasurableSet U)
    (hE : ∀ j i, MeasurableSet (E j i))
    (hCover : U ⊆ ⋃ j ∈ B, ⋃ i ∈ S j, E j i) :
    Kakeya.Conditional.mass μ U ≤
      ∑ j ∈ B, ∑ i ∈ S j, Kakeya.Conditional.mass μ (E j i) := by
  classical
  let P := Σ j : {j : T // j ∈ B}, {i : I // i ∈ S j.val}
  let E' : P → Set X := fun p => E p.1.val p.2.val
  have hCover' : ∀ x ∈ U, ∃ p : P, x ∈ E' p := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hCover hx)
    obtain ⟨hjB, hj⟩ := Set.mem_iUnion.mp hj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hj
    obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨⟨j, hjB⟩, ⟨i, hiS⟩⟩, hxi⟩
  have hMass := Kakeya.Conditional.mass_le_sum μ U E' hU
    (fun p => hE p.1.val p.2.val) hCover'
  have hSum : (∑ p : P, Kakeya.Conditional.mass μ (E' p)) =
      ∑ j ∈ B, ∑ i ∈ S j, Kakeya.Conditional.mass μ (E j i) := by
    calc
      (∑ p : P, Kakeya.Conditional.mass μ (E' p)) =
          ∑ j : {j : T // j ∈ B},
            ∑ i : {i : I // i ∈ S j.val},
              Kakeya.Conditional.mass μ (E j.val i.val) := by
                simp only [P, E', Fintype.sum_sigma]
      _ = ∑ j : {j : T // j ∈ B},
            ∑ i ∈ S j.val, Kakeya.Conditional.mass μ (E j.val i) := by
              apply Finset.sum_congr rfl
              intro j _
              exact Finset.sum_coe_sort (S j.val)
                (fun i => Kakeya.Conditional.mass μ (E j.val i))
      _ = _ := Finset.sum_coe_sort B
        (fun j => ∑ i ∈ S j, Kakeya.Conditional.mass μ (E j i))
  calc
    _ ≤ ∑ p : P, Kakeya.Conditional.mass μ (E' p) := hMass
    _ = _ := hSum

/-- The greedy recurrence controls the mass of the selected union. -/
theorem twoRadius_mass_capture_from_step
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : Set X) (Q : ℕ → Set X) (q N : ℝ)
    (hq : 0 < q) (hqN : q ≤ N)
    (hF : MeasurableSet F)
    (hU : MeasurableSet (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊))
    (hSub : Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊ ⊆ F)
    (hStep : ∀ k, Kakeya.Eighty4.greedyResidual μ F Q (k + 1) ≤
      (1 - q / N) * Kakeya.Eighty4.greedyResidual μ F Q k) :
    Kakeya.Conditional.mass μ F ≤
      (1 / (1 - Real.exp (-1))) *
        Kakeya.Conditional.mass μ (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊) := by
  let R : ℕ → ℝ := fun k => Kakeya.Eighty4.greedyResidual μ F Q k
  have hR0 : R 0 = Kakeya.Conditional.mass μ F := by
    simp [R, Kakeya.Eighty4.greedyResidual, Kakeya.Eighty4.greedyUnion]
  have hRnonneg : 0 ≤ R 0 := by
    rw [hR0]
    exact integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg F x)
  have hGreedy :=
    (Kakeya.Eighty4.greedy_capture_from_recurrence R q N hq hqN hRnonneg hStep).2
  rw [hR0] at hGreedy
  have hSplit : Kakeya.Conditional.mass μ F =
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊) +
        R ⌈N / q⌉₊ := by
    simpa only [R, Kakeya.Eighty4.greedyResidual] using
      (Kakeya.Eighty4.mass_eq_covered_add_residual μ F
        (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊) hF hU hSub)
  have hCancel : Kakeya.Conditional.mass μ F - R ⌈N / q⌉₊ =
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.greedyUnion Q ⌈N / q⌉₊) := by
    linarith
  simpa only [hCancel] using hGreedy

noncomputable def twoRadiusRadius
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    {tubes : T → Set X} (g : ConcreteTubeBallGeometry tubes)
    {μ : Measure X} {n : ℕ} (b : ConcreteTubeBallBounds μ tubes n g)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : ℝ :=
  b.A * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
    (-((1 : ℝ) / ((n : ℝ) - 1)))

/-- Geometric and greedy data for the two-radius endpoint. -/
structure ConcreteTwoRadiusGreedy
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g) where
  hT : ∀ j, MeasurableSet (tubes j)
  hStep : ∀ m k,
    Kakeya.Eighty4.greedyResidual μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) (k + 1) ≤
    (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m /
      (Fintype.card T : ℝ)) *
      Kakeya.Eighty4.greedyResidual μ
        (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) k
  centers : ∀ m, Fin (g.ballCount m) → X
  hBall : ∀ m i,
    g.ball m i = Metric.ball (centers m i) (twoRadiusRadius g b m)
  hVitali : ∀ m,
    Kakeya.Eighty4.greedyUnion (g.greedyQ m)
      ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
    ⋃ j ∈ g.B m, ⋃ i ∈ g.coverIndices m j,
      tubes j ∩ Metric.ball (centers m i) (3 * twoRadiusRadius g b m)
  hTripleCost : ∀ m j i, j ∈ g.B m → i ∈ g.coverIndices m j →
    Kakeya.Conditional.mass μ
      (tubes j ∩ Metric.ball (centers m i) (3 * twoRadiusRadius g b m)) ≤
    b.C * b.deltaPow * twoRadiusRadius g b m

/-- The greedy mass is controlled by the cost of the enlarged Vitali cover. -/
theorem ConcreteTwoRadiusGreedy.mass_capture
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) *
        ((b.C * b.deltaPow * twoRadiusRadius g b m) *
          (((g.B m).card : ℝ) + ((g.P m).card : ℝ))) := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let v : ℝ := b.C * b.deltaPow * twoRadiusRadius g b m
  let U := Kakeya.Eighty4.greedyUnion (g.greedyQ m) ⌈(Fintype.card T : ℝ) / q⌉₊
  have hU : MeasurableSet U := by
    exact Kakeya.Eighty4.greedyUnion_measurable (g.greedyQ m)
      (g.greedyQ_measurable c.hT m) _
  have hSub : U ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m := by
    intro x hx
    change x ∈ ⋃ k ∈ Finset.range ⌈(Fintype.card T : ℝ) / q⌉₊,
      g.greedyQ m k at hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_, hxk⟩ := Set.mem_iUnion.mp hk
    exact g.greedyQ_subset_level m k hxk
  have hGreedy : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * Kakeya.Conditional.mass μ U := by
    exact twoRadius_mass_capture_from_step μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) (g.greedyQ m) q
      (Fintype.card T : ℝ) (Kakeya.Eighty4.dyadicScale_pos _ m)
      (b.hScaleLe m)
      (Kakeya.Eighty4.concreteDyadicBand_measurable tubes c.hT m)
      hU hSub (c.hStep m)
  let E : T → Fin (g.ballCount m) → Set X := fun j i =>
    tubes j ∩ Metric.ball (c.centers m i) (3 * twoRadiusRadius g b m)
  have hE : ∀ j i, MeasurableSet (E j i) := by
    intro j i
    exact (c.hT j).inter Metric.isOpen_ball.measurableSet
  have hMass : Kakeya.Conditional.mass μ U ≤
      ∑ j ∈ g.B m, ∑ i ∈ g.coverIndices m j,
        Kakeya.Conditional.mass μ (E j i) := by
    exact twoRadius_mass_le_double_sum μ (g.B m) (g.coverIndices m) U E
      hU hE (c.hVitali m)
  have hv : 0 ≤ v := by
    dsimp [v, twoRadiusRadius]
    exact mul_nonneg (mul_nonneg b.hC b.hDeltaPow)
      (Kakeya.Eighty9.canonical_dyadic_radius_nonneg n
        (Fintype.card T) b.A b.hA m)
  have hCost : Kakeya.Conditional.mass μ U ≤
      v * (∑ j ∈ g.B m, ((g.coverIndices m j).card : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ g.B m, ∑ i ∈ g.coverIndices m j,
        Kakeya.Conditional.mass μ (E j i) := hMass
      _ ≤ ∑ j ∈ g.B m, ∑ _i ∈ g.coverIndices m j, v := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro i hi
        exact c.hTripleCost m j i hj hi
      _ = v * (∑ j ∈ g.B m, ((g.coverIndices m j).card : ℝ)) := by
        simp [Finset.mul_sum, mul_comm]
  have hLabel : Kakeya.Conditional.mass μ U ≤
      v * (((g.B m).card : ℝ) + ((g.P m).card : ℝ)) :=
    hCost.trans (mul_le_mul_of_nonneg_left (g.coverIndices_card_budget m) hv)
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  exact hGreedy.trans (mul_le_mul_of_nonneg_left hLabel hH)

/-- Theorem 4.6 large-level budget using the triple-radius Vitali mass. -/
theorem paper46_twoRadius_analytic_level_budget
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (a : Paper46LargeLevelInputs μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * b.C *
        (8 * b.Z +
          paper46ExceptionalOverhead μ tubes n
            (g.toBallLocalized μ n b).toRetainedDyadicData * b.deltaPow) *
        twoRadiusRadius g b m := by
  classical
  let s := (g.toBallLocalized μ n b).toRetainedDyadicData
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let H : ℝ := 1 / (1 - Real.exp (-1))
  let E : ℝ := paper46ExceptionalOverhead μ tubes n s
  let U : ℝ := 8 * (Fintype.card T : ℝ) + E
  let v : ℝ := b.C * b.deltaPow * twoRadiusRadius g b m
  let M : ℝ := ((g.B m).card : ℝ) + ((g.P m).card : ℝ)
  have hH : 0 ≤ H := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hv : 0 ≤ v := by
    dsimp [v, twoRadiusRadius]
    exact mul_nonneg (mul_nonneg b.hC b.hDeltaPow)
      (Kakeya.Eighty9.canonical_dyadic_radius_nonneg n
        (Fintype.card T) b.A b.hA m)
  have hCapture : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤ H * (v * M) := by
    exact ConcreteTwoRadiusGreedy.mass_capture μ tubes n g b c m
  have hCount : q * M ≤ U := by
    have hc := paper46_large_level_retained_count μ tubes n s a m hlarge
    have hB : (g.toBallLocalized μ n b).B m = g.B m := rfl
    have hP : (g.toBallLocalized μ n b).P m = g.P m := rfl
    simpa only [q, M, U, E, s, hB, hP] using hc
  have hBound : q * Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤ H * U * v := by
    calc
      _ ≤ q * (H * (v * M)) :=
        mul_le_mul_of_nonneg_left hCapture
          (Kakeya.Eighty4.dyadicScale_pos _ m).le
      _ = (H * v) * (q * M) := by ring
      _ ≤ (H * v) * U :=
        mul_le_mul_of_nonneg_left hCount (mul_nonneg hH hv)
      _ = H * U * v := by ring
  have hCoeff : 0 ≤ H * b.C * twoRadiusRadius g b m := by
    exact mul_nonneg (mul_nonneg hH b.hC)
      (Kakeya.Eighty9.canonical_dyadic_radius_nonneg n
        (Fintype.card T) b.A b.hA m)
  have hNorm : 8 * ((Fintype.card T : ℝ) * b.deltaPow) +
      E * b.deltaPow ≤ 8 * b.Z + E * b.deltaPow := by
    have hh := mul_le_mul_of_nonneg_left b.hNormalization
      (by norm_num : (0 : ℝ) ≤ 8)
    linarith
  change q * Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        H * b.C * (8 * b.Z + E * b.deltaPow) * twoRadiusRadius g b m
  calc
    _ ≤ H * U * v := hBound
    _ = (H * b.C * twoRadiusRadius g b m) *
        (8 * ((Fintype.card T : ℝ) * b.deltaPow) + E * b.deltaPow) := by
          dsimp [U, v]
          ring
    _ ≤ (H * b.C * twoRadiusRadius g b m) *
        (8 * b.Z + E * b.deltaPow) :=
          mul_le_mul_of_nonneg_left hNorm hCoeff
    _ = H * b.C * (8 * b.Z + E * b.deltaPow) *
        twoRadiusRadius g b m := by ring

/-- The triple-radius large-level estimate at the critical dyadic exponent. -/
theorem paper46_twoRadius_large_uniform_level_budget
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (a : Paper46LargeLevelInputs μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * b.C *
        (8 * b.Z + paper46ExceptionalOverhead μ tubes n
          (g.toBallLocalized μ n b).toRetainedDyadicData * b.deltaPow) * b.A := by
  classical
  let s := (g.toBallLocalized μ n b).toRetainedDyadicData
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let alpha : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  let W : ℝ := (1 / (1 - Real.exp (-1))) * s.C *
    (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ alpha := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + alpha) = q * q ^ alpha := by
    rw [Real.rpow_add hq 1 alpha, Real.rpow_one]
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hE := paper46ExceptionalOverhead_nonneg μ tubes n s
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hW : 0 ≤ W := by
    dsimp [W]
    apply mul_nonneg (mul_nonneg hH s.hC)
    exact add_nonneg (mul_nonneg (by norm_num) hZ)
      (mul_nonneg hE s.hDeltaPow)
  have hLevel := paper46_twoRadius_analytic_level_budget
    μ tubes n g b c a m hlarge
  have hScaled := mul_le_mul_of_nonneg_left hLevel hqa
  have hCap := mul_le_mul_of_nonneg_left (s.hRadiusScale m) hW
  have hRadius : s.radius m = twoRadiusRadius g b m := by
    dsimp [s, twoRadiusRadius]
    first
    | rfl
    | simp [ConcreteTubeBallGeometry.toBallLocalized,
        Kakeya.Eighty9.canonical_dyadic_radius, one_div]
    | simp [ConcreteTubeBallGeometry.toBallLocalized, one_div]
  have hC : s.C = b.C := rfl
  have hZeq : s.Z = b.Z := rfl
  have hDelta : s.deltaPow = b.deltaPow := rfl
  change q ^ (1 + alpha) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      W * s.radiusCap
  calc
    _ = (q ^ alpha) *
        (q * Kakeya.Conditional.mass μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
            rw [hpow]
            ring
    _ ≤ (q ^ alpha) * (W * s.radius m) := by
      simpa only [q, W, hC, hZeq, hDelta, hRadius,
        twoRadiusRadius, one_div] using hScaled
    _ = W * (q ^ alpha * s.radius m) := by ring
    _ ≤ W * s.radiusCap := hCap

/-- Uniform dyadic budget using triple-radius covering and radius-R counting. -/
theorem paper46_twoRadius_analytic_uniform_level_budget
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ) (hn : 2 ≤ n)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (a : Paper46LargeLevelInputs μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      paper46EndpointBudget μ tubes n
        (g.toBallLocalized μ n b).toRetainedDyadicData a.cutoff := by
  let s := (g.toBallLocalized μ n b).toRetainedDyadicData
  have hmass : 0 ≤ Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg _ x)
  have hsmallNonneg : 0 ≤ a.cutoff ^ (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [a.hCutoff]) _) hmass
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hE := paper46ExceptionalOverhead_nonneg μ tubes n s
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hCap : 0 ≤ s.radiusCap := by
    exact (mul_nonneg (Real.rpow_nonneg
      (Kakeya.Eighty4.dyadicScale_pos _ m).le _) (s.hRadiusNonneg m)).trans
        (s.hRadiusScale m)
  have hlargeNonneg : 0 ≤ (1 / (1 - Real.exp (-1))) * s.C *
      (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
        s.radiusCap :=
    mul_nonneg (mul_nonneg (mul_nonneg hH s.hC)
      (add_nonneg (mul_nonneg (by norm_num) hZ)
        (mul_nonneg hE s.hDeltaPow))) hCap
  unfold paper46EndpointBudget
  by_cases hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  · exact (paper46_twoRadius_large_uniform_level_budget
      μ tubes n g b c a m hlarge).trans
        (le_add_of_nonneg_right hsmallNonneg)
  · have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
      apply div_nonneg (by norm_num)
      linarith
    exact (paper46_small_level_budget μ tubes ((1 : ℝ) / ((n : ℝ) - 1))
      ha c.hT m a.cutoff (lt_of_not_ge hlarge)).trans
        (le_add_of_nonneg_left hlargeNonneg)

/-- The critical Kakeya moment estimate from the two-radius Vitali endpoint. -/
theorem full_conditional_kakeya_moment_of_paper46_twoRadius
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ) (hn : 2 ≤ n)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (a : Paper46LargeLevelInputs μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46EndpointBudget μ tubes n
          (g.toBallLocalized μ n b).toRetainedDyadicData a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg (by norm_num)
    linarith
  have h := Kakeya.Eighty9.logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1))
    (paper46EndpointBudget μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData a.cutoff)
    ha c.hT
    (paper46_twoRadius_analytic_uniform_level_budget μ tubes n hn g b c a)
  rw [(Kakeya.Conditional.dimension_exponents n hn).1] at h
  exact h

/-- The norm estimate with the two-radius analytic budget. -/
theorem full_conditional_kakeya_of_paper46_twoRadius
    {X T : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
    [Fintype T] (μ : Measure X) [IsFiniteMeasure μ]
    (tubes : T → Set X) (n : ℕ) (hn : 2 ≤ n)
    (g : ConcreteTubeBallGeometry tubes)
    (b : ConcreteTubeBallBounds μ tubes n g)
    (c : ConcreteTwoRadiusGreedy μ tubes n g b)
    (a : Paper46LargeLevelInputs μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46EndpointBudget μ tubes n
          (g.toBallLocalized μ n b).toRetainedDyadicData a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((n : ℝ) - 1) / (n : ℝ)) := by
  exact Kakeya.Eighty9.logarithmic_norm_from_level_budgets μ tubes n hn
    (paper46EndpointBudget μ tubes n
      (g.toBallLocalized μ n b).toRetainedDyadicData a.cutoff) c.hT
    (paper46_twoRadius_analytic_uniform_level_budget μ tubes n hn g b c a)

end Kakeya.Ninety21
