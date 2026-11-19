module

public import Kakeya.Ninety21AngularGramGeometry

/-!
# Quantitative packing in the projected angular caps

Volume comparison for a finite separated family in Euclidean dimension `k+1`
gives the exponent `k+1`. Applied to the two sheets of a spherical cap,
this yields the quantitative bound used by the exceptional-piece budget.
-/

@[expose] public section

namespace Kakeya.Ninety21

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Disjoint small balls give the Euclidean polynomial packing estimate.
The positive finite unit-ball mass and the ball-volume identity are
parameters of the measure; for Euclidean volume these are standard facts. -/
theorem finite_euclidean_packing_of_ball_volume
    {k : ℕ} {I : Type*}
    (point : I → Kakeya.Space (k + 1)) (J : Finset I)
    (s θ : ℝ) (hs : 0 < s) (hθ : 0 ≤ θ)
    (μ : Measure (Kakeya.Space (k + 1))) (κ : ENNReal)
    (hκpos : 0 < κ) (hκfinite : κ ≠ ⊤)
    (hBall : ∀ (x : Kakeya.Space (k + 1)) (r : ℝ), 0 < r →
      μ (Metric.ball x r) = ENNReal.ofReal (r ^ (k + 1)) * κ)
    (hSeparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      s ≤ dist (point i) (point j))
    (hSmall : ∀ i ∈ J, ‖point i‖ ≤ θ) :
    (J.card : ℝ) ≤ (1 + 2 * θ / s) ^ (k + 1) := by
  classical
  let r : ℝ := s / 2
  let ρ : ℝ := θ + r
  have hr : 0 < r := by dsimp [r]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  let U : Set (Kakeya.Space (k + 1)) :=
    ⋃ i ∈ J, Metric.ball (point i) r
  have hDisjoint : (↑J : Set I).PairwiseDisjoint
      (fun i => Metric.ball (point i) r) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have ha : dist (point i) x < r := by
      simpa only [dist_comm] using (Metric.mem_ball.mp hxi)
    have hb : dist x (point j) < r := Metric.mem_ball.mp hxj
    have htri := dist_triangle (point i) x (point j)
    have hsep := hSeparated i hi j hj hij
    dsimp [r] at ha hb
    linarith
  have hSubset : U ⊆ Metric.ball (0 : Kakeya.Space (k + 1)) ρ := by
    intro x hx
    change x ∈ ⋃ i ∈ J, Metric.ball (point i) r at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hcx : dist x (point i) < r := by
      simpa only [dist_comm] using (Metric.mem_ball.mp hxi)
    have hcenter : dist (point i) (0 : Kakeya.Space (k + 1)) ≤ θ := by
      simpa only [dist_zero_right] using hSmall i hi
    have ht := dist_triangle x (point i) (0 : Kakeya.Space (k + 1))
    apply Metric.mem_ball.mpr
    dsimp [ρ]
    linarith
  have hMass : (J.card : ENNReal) *
        (ENNReal.ofReal (r ^ (k + 1)) * κ) ≤
        ENNReal.ofReal (ρ ^ (k + 1)) * κ := by
    calc
      (J.card : ENNReal) * (ENNReal.ofReal (r ^ (k + 1)) * κ) =
          ∑ i ∈ J, μ (Metric.ball (point i) r) := by
            simp [hBall _ _ hr, Finset.sum_const, nsmul_eq_mul]
      _ = μ U := by
        symm
        exact measure_biUnion_finset hDisjoint
          (fun _ _ => measurableSet_ball)
      _ ≤ μ (Metric.ball 0 ρ) := measure_mono hSubset
      _ = ENNReal.ofReal (ρ ^ (k + 1)) * κ := hBall 0 ρ hρ
  have hCancel : (J.card : ENNReal) *
      ENNReal.ofReal (r ^ (k + 1)) ≤
      ENNReal.ofReal (ρ ^ (k + 1)) := by
    apply (ENNReal.mul_le_mul_iff_left hκpos.ne' hκfinite).1
    simpa only [mul_assoc] using hMass
  have hFiniteρ : ENNReal.ofReal (ρ ^ (k + 1)) ≠ ⊤ := by simp
  have hFinite : (J.card : ENNReal) *
      ENNReal.ofReal (r ^ (k + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFiniteρ hCancel
  have hReal : (J.card : ℝ) * r ^ (k + 1) ≤ ρ ^ (k + 1) := by
    have h := (ENNReal.toReal_le_toReal hFinite hFiniteρ).2 hCancel
    simpa [ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      ENNReal.toReal_ofReal (pow_nonneg hρ.le _)] using h
  have hCard : (J.card : ℝ) ≤ ρ ^ (k + 1) / r ^ (k + 1) :=
    (le_div_iff₀ (pow_pos hr _)).2 hReal
  have hRatio : ρ / r = 1 + 2 * θ / s := by
    dsimp [ρ, r]
    field_simp [ne_of_gt hs]
    ring
  calc
    (J.card : ℝ) ≤ ρ ^ (k + 1) / r ^ (k + 1) := hCard
    _ = (ρ / r) ^ (k + 1) := (div_pow ρ r (k + 1)).symm
    _ = (1 + 2 * θ / s) ^ (k + 1) := by rw [hRatio]

/-- The ball-mass hypotheses follow from standard Euclidean volume.
The `Fin (k+1)` coordinate space has positive dimension. -/
theorem finite_euclidean_projected_packing
    {k : ℕ} {I : Type*}
    (point : I → Kakeya.Space (k + 1)) (J : Finset I)
    (s θ : ℝ) (hs : 0 < s) (hθ : 0 ≤ θ)
    (hSeparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      s ≤ dist (point i) (point j))
    (hSmall : ∀ i ∈ J, ‖point i‖ ≤ θ) :
    (J.card : ℝ) ≤ (1 + 2 * θ / s) ^ (k + 1) := by
  let μ : Measure (Kakeya.Space (k + 1)) := volume
  let κ : ENNReal := μ (Metric.ball (0 : Kakeya.Space (k + 1)) 1)
  have hκpos : 0 < κ := by
    change 0 < (volume : Measure (Kakeya.Space (k + 1)))
      (Metric.ball (0 : Kakeya.Space (k + 1)) 1)
    exact Metric.isOpen_ball.measure_pos volume
      ⟨(0 : Kakeya.Space (k + 1)), Metric.mem_ball_self (by norm_num)⟩
  have hκfinite : κ ≠ ⊤ := measure_ball_lt_top.ne
  have hBall : ∀ (x : Kakeya.Space (k + 1)) (r : ℝ), 0 < r →
      μ (Metric.ball x r) = ENNReal.ofReal (r ^ (k + 1)) * κ := by
    intro x r hr
    have h1 := EuclideanSpace.volume_ball (Fin (k + 1)) x r
    have h0 := EuclideanSpace.volume_ball (Fin (k + 1))
      (0 : Kakeya.Space (k + 1)) 1
    dsimp [μ, κ]
    rw [h1, h0]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.ofReal_pow hr.le]
  exact finite_euclidean_packing_of_ball_volume
    point J s θ hs hθ μ κ hκpos hκfinite hBall hSeparated hSmall

/-- Quantitative two-chart packing, with one projected Euclidean ball on
each sign sheet. -/
theorem separated_two_chart_real_card_le
    {k : ℕ} {I : Type*}
    (point : I → Kakeya.Space (k + 2))
    (projection : I → Kakeya.Space (k + 1))
    (side : I → Bool) (J : Finset I)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hSeparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ε ≤ dist (point i) (point j))
    (hSmall : ∀ i ∈ J, ‖projection i‖ ≤ θ)
    (hReverse : ∀ i ∈ J, ∀ j ∈ J, side i = side j →
      dist (point i) (point j) ≤ 2 * dist (projection i) (projection j)) :
    (J.card : ℝ) ≤ 2 * (1 + 4 * θ / ε) ^ (k + 1) := by
  classical
  let Jpos := J.filter (fun i => side i = true)
  let Jneg := J.filter (fun i => side i ≠ true)
  have hSepSide (K : Finset I) (hK : K ⊆ J)
      (hSide : ∀ i ∈ K, ∀ j ∈ K, side i = side j) :
      ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
        ε / 2 ≤ dist (projection i) (projection j) := by
    intro i hi j hj hij
    have hse := hSeparated i (hK hi) j (hK hj) hij
    have hrev := hReverse i (hK hi) j (hK hj) (hSide i hi j hj)
    linarith
  have hPosSub : Jpos ⊆ J := Finset.filter_subset _ _
  have hNegSub : Jneg ⊆ J := Finset.filter_subset _ _
  have hPosSame : ∀ i ∈ Jpos, ∀ j ∈ Jpos, side i = side j := by
    intro i hi j hj
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  have hNegSame : ∀ i ∈ Jneg, ∀ j ∈ Jneg, side i = side j := by
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    cases hiS : side i <;> cases hjS : side j <;> simp_all
  have hPos := finite_euclidean_projected_packing
    projection Jpos (ε / 2) θ (by positivity) hθ
    (hSepSide Jpos hPosSub hPosSame)
    (fun i hi => hSmall i (hPosSub hi))
  have hNeg := finite_euclidean_projected_packing
    projection Jneg (ε / 2) θ (by positivity) hθ
    (hSepSide Jneg hNegSub hNegSame)
    (fun i hi => hSmall i (hNegSub hi))
  have hPartition : Jpos.card + Jneg.card = J.card :=
    Finset.card_filter_add_card_filter_not (s := J) (fun i => side i = true)
  have hRatio : 1 + 2 * θ / (ε / 2) = 1 + 4 * θ / ε := by
    field_simp [ne_of_gt hε]
    ring
  rw [hRatio] at hPos hNeg
  have hPartitionReal : (J.card : ℝ) =
      (Jpos.card : ℝ) + (Jneg.card : ℝ) := by
    exact_mod_cast hPartition.symm
  calc
    (J.card : ℝ) = (Jpos.card : ℝ) + (Jneg.card : ℝ) := hPartitionReal
    _ ≤ (1 + 4 * θ / ε) ^ (k + 1) +
        (1 + 4 * θ / ε) ^ (k + 1) := add_le_add hPos hNeg
    _ = 2 * (1 + 4 * θ / ε) ^ (k + 1) := by ring

/-- The actual nontransverse index set satisfies the quantitative cap
estimate once the orthogonal two-chart coordinates are supplied. -/
theorem quantitative_cap_card_of_projected_chart
    {k : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space (k + 2))
    (projection : T → T → Kakeya.Space (k + 1))
    (side : T → T → Bool)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hSmall : ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ)
    (hReverse : ∀ r i j : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
      j ∈ nonTransverseDirectionIndices direction θ r →
      side r i = side r j →
      dist (direction i) (direction j) ≤
        2 * dist (projection r i) (projection r j)) :
    ∀ r : T,
      ((nonTransverseDirectionIndices direction θ r).card : ℝ) ≤
        2 * (1 + 4 * θ / ε) ^ (k + 1) := by
  intro r
  let J := nonTransverseDirectionIndices direction θ r
  exact separated_two_chart_real_card_le direction
    (projection r) (side r) J ε θ hε hθ
    (by intro i hi j hj hij; exact hSeparated i j hij)
    (by intro i hi; exact hSmall r i hi)
    (by intro i hi j hj hSide; exact hReverse r i j hi hj hSide)

end Kakeya.Ninety21
