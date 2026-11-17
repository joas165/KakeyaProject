module

public import Kakeya.Ninety21ParentVitaliPacking
public import Kakeya.Ninety21GreedyVitaliEndpointBridge

/-!
# Geometric packing for the canonical greedy–Vitali construction

The original-tube incidence constant follows from the disjoint Vitali
selection, the canonical dyadic radius, and the length-one tube geometry.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- The canonical dyadic radius does not exceed its radius coefficient. -/
theorem canonicalGreedyVitaliRadius_le_coefficient
    {T : Type*} [Fintype T] (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    canonicalGreedyVitaliRadius (T := T) (k + 2) A m ≤ A := by
  have hq : (1 : ℝ) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m := by
    unfold Kakeya.Eighty4.dyadicScale
    exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2) :
      (1 : ℕ) ≤ 2 ^ m.val)
  have hden : 0 < (((k + 2 : ℕ) : ℝ) - 1) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  have he : -((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ 0 := by
    have : 0 ≤ (1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1) :=
      div_nonneg (by norm_num) hden.le
    linarith
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hq he
  unfold canonicalGreedyVitaliRadius
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left hpow hA)

/-- A total-tube scale bound ensures `δ ≤ R_m` at every dyadic level. -/
theorem delta_le_canonicalGreedyVitaliRadius_of_total_scale
    {T : Type*} [Fintype T] [Nonempty T] (k : ℕ)
    (A δ : ℝ) (hδ : 0 ≤ δ)
    (hTotal : δ * (Fintype.card T : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    δ ≤ canonicalGreedyVitaliRadius (T := T) (k + 2) A m := by
  let e : ℝ := (1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  have hden : 0 < (((k + 2 : ℕ) : ℝ) - 1) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  have he : 0 ≤ e := div_nonneg (by norm_num) hden.le
  have hqpos : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqN : q ≤ (Fintype.card T : ℝ) :=
    dyadicScale_le_card (T := T) m
  have hpow : q ^ e ≤ (Fintype.card T : ℝ) ^ e :=
    Real.rpow_le_rpow hqpos.le hqN he
  have hδq : δ * q ^ e ≤ A := by
    calc
      δ * q ^ e ≤ δ * (Fintype.card T : ℝ) ^ e :=
        mul_le_mul_of_nonneg_left hpow hδ
      _ ≤ A := hTotal
  have hscale : q ^ e *
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m = A := by
    exact canonicalGreedyVitaliRadius_scale (T := T) (k + 2) A m
  have hpowpos : 0 < q ^ e := Real.rpow_pos_of_pos hqpos e
  apply (mul_le_mul_iff_left₀ hpowpos).mp
  calc
    δ * q ^ e ≤ A := hδq
    _ = q ^ e * canonicalGreedyVitaliRadius (T := T) (k + 2) A m :=
      hscale.symm
    _ = canonicalGreedyVitaliRadius (T := T) (k + 2) A m * q ^ e :=
      mul_comm _ _

/-- Cancellation of the transverse volume factor with `R ≤ A`.
The coefficient is valid for all positive values of `A`. -/
theorem disjoint_balls_card_le_dyadic_with_radius_coefficient
    (k M : ℕ) (R A q ωn ωtrans : ℝ)
    (hR : 0 < R) (hRA : R ≤ A) (hA : 0 < A) (hq : 0 < q)
    (hωn : 0 < ωn) (hωtrans : 0 ≤ ωtrans)
    (hScale : q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) * R = A)
    (hVolume : (M : ℝ) * (R ^ (k + 2) * ωn) ≤
      (1 + 6 * R) * ((3 * R) ^ (k + 1) * ωtrans)) :
    (M : ℝ) ≤
      (((1 + 6 * A) * 3 ^ (k + 1) * ωtrans) / (ωn * A)) *
        q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
  let e : ℝ := (1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)
  let W : ℝ := (1 + 6 * A) * 3 ^ (k + 1) * ωtrans
  have hpow : 0 < R ^ (k + 1) := pow_pos hR _
  have hfactor : ((M : ℝ) * ωn * R) * R ^ (k + 1) ≤
      W * R ^ (k + 1) := by
    calc
      ((M : ℝ) * ωn * R) * R ^ (k + 1) =
          (M : ℝ) * (R ^ (k + 2) * ωn) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ (1 + 6 * R) * ((3 * R) ^ (k + 1) * ωtrans) := hVolume
      _ = ((1 + 6 * R) * 3 ^ (k + 1) * ωtrans) * R ^ (k + 1) := by
        rw [mul_pow]
        ring
      _ ≤ W * R ^ (k + 1) := by
        have hbound : 1 + 6 * R ≤ 1 + 6 * A := by linarith
        have hnonneg : 0 ≤ 3 ^ (k + 1) * ωtrans * R ^ (k + 1) := by
          positivity
        dsimp [W]
        nlinarith [mul_le_mul_of_nonneg_right hbound hnonneg]
  have hbasic : (M : ℝ) * ωn * R ≤ W :=
    (mul_le_mul_iff_left₀ hpow).mp hfactor
  have hqnonneg : 0 ≤ q ^ e :=
    (Real.rpow_pos_of_pos hq e).le
  have hscaled : (M : ℝ) * (ωn * A) ≤ W * q ^ e := by
    calc
      (M : ℝ) * (ωn * A) = ((M : ℝ) * ωn * R) * q ^ e := by
        rw [← hScale]
        ring
      _ ≤ W * q ^ e := mul_le_mul_of_nonneg_right hbasic hqnonneg
  have hfinal := (le_div_iff₀ (mul_pos hωn hA)).mpr hscaled
  calc
    (M : ℝ) ≤ W * q ^ e / (ωn * A) := hfinal
    _ = (W / (ωn * A)) *
        q ^ ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
      dsimp [e]
      ring

/-- The canonical Vitali selection satisfies the numerical packing bound
for unit-length original tubes. -/
theorem ConcreteGreedyVitaliCandidates.selected_card_le_of_canonical_geometry
    {k : ℕ} {T : Type*} [Fintype T]
    (center direction : T → Kakeya.Space (k + 2))
    (δ A : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun r => Kakeya.unitTube (center r) (direction r) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun r => Kakeya.unitTube (center r) (direction r) δ) g)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hA : 0 < A)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hδR : ∀ m, δ ≤ d.radius m)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (r : T) (hr : r ∈ g.B m) :
    ((d.selected m r).card : ℝ) ≤
      (((1 + 6 * A) * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
        (packingBallConstant (k + 2) * A)) *
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
  let R := d.radius m
  have hv : direction r ≠ 0 := by
    intro hz
    have h := hUnit r
    simp [hz] at h
  have hNorm : ‖direction r‖ ≤ 1 := (hUnit r).le
  have hR : 0 < R := d.hRadius m
  have hRA : R ≤ A := by
    change d.radius m ≤ A
    rw [hRadius m]
    exact canonicalGreedyVitaliRadius_le_coefficient k A hA.le m
  have hDisjoint :
      (↑(d.selected m r) : Set (Fin (g.ballCount m))).PairwiseDisjoint
        (fun i => Metric.ball (d.centers m i) R) := by
    intro i hi j hj hij
    have h := d.selected_disjoint m r hr i hi j hj hij
    simpa only [d.hBall m i, d.hBall m j] using h
  have hHit (i : Fin (g.ballCount m)) (hi : i ∈ d.selected m r) :
      (Metric.ball (d.centers m i) R ∩
        Kakeya.unitTube (center r) (direction r) δ).Nonempty := by
    simpa only [d.hBall m i] using
      (d.selected_ball_meets_parent_tube m r hr i hi)
  have hVolume := originalTube_disjoint_balls_real_volume_le k
    (center r) (direction r) δ R (d.centers m) (d.selected m r)
    hv hNorm hR (hδR m) hDisjoint hHit
  have hScale :
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) * R = A := by
    dsimp [R]
    rw [hRadius m]
    exact canonicalGreedyVitaliRadius_scale (T := T) (k + 2) A m
  exact disjoint_balls_card_le_dyadic_with_radius_coefficient
    k (d.selected m r).card R A
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (packingBallConstant (k + 2)) (packingBallConstant (k + 1))
    hR hRA hA (Kakeya.Eighty4.dyadicScale_pos _ m)
    (packingBallConstant_pos _) (packingBallConstant_pos _).le
    hScale hVolume

/-- Maximal-unused greedy bounds with parent-associated `hHallRight`
obtained from the actual tube-wise Vitali selection. -/
noncomputable def ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnusedGeometry
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun r => Kakeya.unitTube (center r) (direction r) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun r => Kakeya.unitTube (center r) (direction r) δ) g)
    (hT : ∀ r, MeasurableSet
      (Kakeya.unitTube (center r) (direction r) δ))
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCgeom : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hTotalRadius : δ * (Fintype.card T : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand
        (fun r => Kakeya.unitTube (center r) (direction r) δ) m)
    (hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ) m)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z) :
    ConcreteTubeBallBounds μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ)
      (k + 2) d.retained := by
  let K : ℝ := ((1 + 6 * A) * 3 ^ (k + 1) * packingBallConstant (k + 1)) /
    (packingBallConstant (k + 2) * A)
  have hK : 0 ≤ K := by
    have hωn := packingBallConstant_pos (k + 2)
    have hωtrans := packingBallConstant_pos (k + 1)
    dsimp [K]
    positivity
  have hv : ∀ r, direction r ≠ 0 := by
    intro r hz
    have h := hUnit r
    simp [hz] at h
  have hRadius' : ∀ m, d.radius m = A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1))) := by
    intro m
    simpa only [canonicalGreedyVitaliRadius] using hRadius m
  have hSelected : ∀ m, (g.B m).card ≤
      ⌈(Fintype.card T : ℝ) /
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ := by
    intro m
    exact g.selected_card_of_maximal_unused_subset μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ) hB m
  have hδR : ∀ m, δ ≤ d.radius m := by
    intro m
    rw [hRadius m]
    exact delta_le_canonicalGreedyVitaliRadius_of_total_scale k
      A δ hδ hTotalRadius m
  have hPacking : ∀ m r, r ∈ g.B m →
      ((d.selected m r).card : ℝ) ≤
        K * Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
          ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) := by
    intro m r hr
    exact d.selected_card_le_of_canonical_geometry
      center direction δ A g hUnit hA hRadius hδR m r hr
  exact d.euclideanTubeBallBounds_of_selected_packing
    μ center direction δ hδ g hT hv hDom
    A C Z K hA.le hC hK hCgeom hRadius' hCenters
    (fun m => dyadicScale_le_card (T := T) m)
    hSelected hNorm hPacking

/-- The derived geometric bounds feed directly into the canonical
TwoRadiusGreedy endpoint without a separate incidence input. -/
noncomputable def ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclideanGeometry
    {k : ℕ} {T : Type*} [Fintype T] [Nonempty T]
    (μ : Measure (Kakeya.Space (k + 2))) [IsFiniteMeasure μ]
    (center direction : T → Kakeya.Space (k + 2))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (g : ConcreteTubeBallGeometry
      (fun r => Kakeya.unitTube (center r) (direction r) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun r => Kakeya.unitTube (center r) (direction r) δ) g)
    (hT : ∀ r, MeasurableSet
      (Kakeya.unitTube (center r) (direction r) δ))
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hDom : ∀ E : Set (Kakeya.Space (k + 2)),
      μ E ≤ (volume : Measure (Kakeya.Space (k + 2))) E)
    (A C Z : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hCpiece : 2 * tripleRadiusTransverseCoefficient k ≤ C)
    (hCtriple : 6 * tripleRadiusTransverseCoefficient k ≤ C)
    (hRadius : ∀ m, d.radius m =
      canonicalGreedyVitaliRadius (T := T) (k + 2) A m)
    (hTotalRadius : δ * (Fintype.card T : ℝ) ^
      ((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)) ≤ A)
    (hCenters : ∀ m i, d.centers m i ∈
      Kakeya.Eighty4.concreteDyadicBand
        (fun r => Kakeya.unitTube (center r) (direction r) δ) m)
    (hB : ∀ m, g.B m ⊆ maximalUnusedDyadicSelected μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ) m)
    (hCanonical : ∀ m, g.chosen m = maximalUnusedDyadicChosen μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ) m)
    (hNorm : (Fintype.card T : ℝ) * δ ^ (k + 1) ≤ Z) :
    let b := d.euclideanBoundsOfMaximalUnusedGeometry
      μ center direction δ hδ g hT hUnit hDom A C Z
      hA hC hCpiece hRadius hTotalRadius hCenters hB hNorm
    ConcreteTwoRadiusGreedy μ
      (fun r => Kakeya.unitTube (center r) (direction r) δ)
      (k + 2) d.retained b := by
  dsimp only
  let b := d.euclideanBoundsOfMaximalUnusedGeometry
    μ center direction δ hδ g hT hUnit hDom A C Z
    hA hC hCpiece hRadius hTotalRadius hCenters hB hNorm
  have hv : ∀ r, direction r ≠ 0 := by
    intro r hz
    have h := hUnit r
    simp [hz] at h
  have hRadius' : ∀ m, d.radius m = twoRadiusRadius d.retained b m := by
    intro m
    change d.radius m = b.A *
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ^
        (-((1 : ℝ) / (((k + 2 : ℕ) : ℝ) - 1)))
    rw [hRadius m]
    rfl
  have hDeltaPow : b.deltaPow = δ ^ (k + 1) := rfl
  have hCgeom : 6 * tripleRadiusTransverseCoefficient k ≤ b.C := hCtriple
  exact ConcreteTwoRadiusGreedy.ofCanonicalVitaliEuclidean μ center direction
    δ hδ g d b (Fintype.card_pos) hCanonical hT hv hDom
    hRadius' hDeltaPow hCgeom

end Kakeya.Ninety21
