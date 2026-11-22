module

public import Kakeya.Ninety21ActualAngularPackingEndpoint

@[expose] public section

namespace Kakeya.Ninety109

open Kakeya.Ninety21
open scoped BigOperators NNReal
section
attribute [local instance] Classical.propDecidable

noncomputable def incidence {X T L : Type*} [Fintype T]
    (tube : T → Set X) (P : L → Set X) (r : L) : Finset T :=
  Finset.univ.filter fun ℓ => (tube ℓ ∩ P r).Nonempty

private theorem axis_dist {n : ℕ} (p u : Space n) (hu : ‖u‖ = 1) (a b : ℝ) :
    dist (p + a • u) (p + b • u) = |a - b| := by
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one,
    Real.norm_eq_abs]

private theorem shell_packing {d : ℕ} {L : Type*} (J : Finset L)
    (p u : Space (d + 1)) (hu : ‖u‖ = 1) (center : L → Space (d + 1))
    (t : L → ℝ) (a ρ : ℝ) (hρ : 0 < ρ)
    (hclose : ∀ r ∈ J, dist (center r) (p + t r • u) ≤ 4 * ρ)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ρ ≤ dist (center i) (center j))
    (hbin : ∀ r ∈ J, |t r - a| ≤ ρ) :
    (J.card : ℝ) ≤ 11 ^ (d + 1) := by
  let z := p + a • u
  have h := finite_euclidean_projected_packing (fun r => center r - z) J
    ρ (5 * ρ) hρ (by positivity)
    (by simpa using hsep) (by
      intro r hr
      rw [← dist_eq_norm]
      have hh := dist_triangle (center r) (p + t r • u) z
      simp only [z, axis_dist p u hu] at hh
      linarith [hclose r hr, hbin r hr])
  have he : 1 + 2 * (5 * ρ) / ρ = 11 := by field_simp; ring
  simpa only [he] using h

private theorem far_overlap {d : ℕ} {T L : Type*} [Fintype T]
    (p v : T → Space (d + 2)) (b : T) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hu : ∀ i, ‖v i‖ = 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (P : L → Set (Space (d + 2))) (r s : L) (a a' : ℝ)
    (hr : ∀ x ∈ P r, x ∈ unitTube (p b) (v b) δ ∧ dist x (p b + a • v b) ≤ 7 * ρ)
    (hs : ∀ x ∈ P s, x ∈ unitTube (p b) (v b) δ ∧ dist x (p b + a' • v b) ≤ 7 * ρ)
    (k : ℕ) (hk : 128 ≤ k) (hl : k * ρ ≤ |a - a'|) (hh : |a - a'| ≤ 1) :
    let I := incidence (fun i => unitTube (p i) (v i) δ) P
    ((I r ∩ I s).card : ℝ) ≤ 2 * 257 ^ (d + 1) * (ρ ^ (d + 1))⁻¹ * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  dsimp only
  let θ := 64 * δ / (k * ρ)
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hk' : (128 : ℝ) ≤ k := by exact_mod_cast hk
  have hkr : 0 < (k : ℝ) * ρ := mul_pos (by linarith) hρ
  have ht : 0 < θ := div_pos (by positivity) hkr
  have hth : θ ≤ 1 / 2 := by
    apply (div_le_iff₀ hkr).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hρ.le]
  have sub : incidence (fun i => unitTube (p i) (v i) δ) P r ∩
      incidence (fun i => unitTube (p i) (v i) δ) P s ⊆ nonTransverseDirectionIndices v θ b := by
    intro i hi
    obtain ⟨hir, his⟩ := Finset.mem_inter.mp hi
    obtain ⟨x, hxi, hxr⟩ := (Finset.mem_filter.mp hir).2
    obtain ⟨y, hyi, hys⟩ := (Finset.mem_filter.mp his).2
    obtain ⟨hxb, hx⟩ := hr x hxr
    obtain ⟨hyb, hy⟩ := hs y hys
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun htrans => ?_⟩
    have hd := two_transverse_tubes_ball_center_diameter (p b) (p i) (v b) (v i)
      x y δ δ θ ht le_rfl (hu b) htrans
      ⟨x, Metric.mem_ball_self hδ, hxb⟩ ⟨x, Metric.mem_ball_self hδ, hxi⟩
      ⟨y, Metric.mem_ball_self hδ, hyb⟩ ⟨y, Metric.mem_ball_self hδ, hyi⟩
    have ha := dist_triangle (p b + a • v b) x (p b + a' • v b)
    rw [axis_dist _ _ (hu b), dist_comm _ x] at ha
    have hb := dist_triangle x y (p b + a' • v b)
    have he : (4 + 8 / θ) * δ = 4 * δ + k * ρ / 8 := by
      dsimp [θ]; field_simp; ring
    rw [he] at hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hk') hρ.le]
  have hc := original_unit_directions_quantitative_cap_card v δ θ hδ ht hth hu hsep b
  have hb : 1 + 4 * θ / δ ≤ 257 / (k * ρ) := by
    dsimp [θ]
    field_simp
    nlinarith
  calc
    _ ≤ ((nonTransverseDirectionIndices v θ b).card : ℝ) := by
      exact_mod_cast Finset.card_le_card sub
    _ ≤ _ := hc
    _ ≤ 2 * (257 / (k * ρ)) ^ (d + 1) := by gcongr
    _ = _ := by rw [div_pow, mul_pow]; ring

noncomputable def overlapConstant (d : ℕ) : ℝ :=
  2 * 11 ^ (d + 2) * (128 + 2 * 257 ^ (d + 1) * ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹)

private theorem overlapConstant_nonneg (d : ℕ) : 0 ≤ overlapConstant d := by
  unfold overlapConstant
  have hp : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹ := tsum_nonneg (fun _ => by positivity)
  positivity

noncomputable def dyadicOverlapConstant (d : ℕ) (C : ℝ) : ℝ :=
  overlapConstant d * (1 + (C ^ (d + 1))⁻¹)

theorem fixed_parent_overlap {d : ℕ} (hd : 1 ≤ d)
    {T L : Type*} [Fintype T] [DecidableEq L]
    (p v : T → Space (d + 2)) (b : T) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (_hρ1 : ρ ≤ 1)
    (hu : ∀ i, ‖v i‖ = 1) (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (J : Finset L) (center : L → Space (d + 2)) (P : L → Set (Space (d + 2)))
    (hball : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (Metric.ball (center i) ρ) (Metric.ball (center j) ρ))
    (hne : ∀ r ∈ J, (P r).Nonempty)
    (hP : ∀ r ∈ J, P r ⊆ unitTube (p b) (v b) δ ∩ Metric.ball (center r) (3 * ρ))
    (s : L) (hs : s ∈ J) :
    let I := incidence (fun i => unitTube (p i) (v i) δ) P
    ∑ r ∈ J.erase s, ((I r ∩ I s).card : ℝ) ≤
      overlapConstant d * ((I s).card + (ρ ^ (d + 1))⁻¹) := by
  classical
  let I := incidence (fun i => unitTube (p i) (v i) δ) P
  let A := J.erase s
  let f := fun r => ((I r ∩ I s).card : ℝ)
  change ∑ r ∈ A, f r ≤ _
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have haxis (r : L) : ∃ t : ℝ, |t| ≤ 1 / 2 ∧
      (r ∈ J → dist (center r) (p b + t • v b) ≤ 4 * ρ) := by
    by_cases h : r ∈ J
    · obtain ⟨x, hx⟩ := hne r h
      obtain ⟨ht, hxball⟩ := hP r h hx
      obtain ⟨a, ha, hc⟩ := originalTube_ball_center_near_axis _ _ _ δ (3 * ρ)
        ⟨x, hxball, ht⟩
      exact ⟨a, ha, fun _ => by linarith⟩
    · exact ⟨0, by norm_num, by simp [h]⟩
  choose t hlen hclose using haxis
  have hpoints (r) (hr : r ∈ J) (x) (hx : x ∈ P r) :
      x ∈ unitTube (p b) (v b) δ ∧ dist x (p b + t r • v b) ≤ 7 * ρ := by
    obtain ⟨h1, h2⟩ := hP r hr hx
    refine ⟨h1, ?_⟩
    linarith [dist_triangle x (center r) (p b + t r • v b), Metric.mem_ball.mp h2,
      hclose r hr]
  let bin := fun r => ⌊|t r - t s| / ρ⌋₊
  let K := A.image bin
  let S := fun k => A.filter (fun r => bin r = k)
  have memJ {k r} (hr : r ∈ S k) : r ∈ J :=
    Finset.mem_of_mem_erase (Finset.mem_filter.mp hr).1
  have bounds {k r} (hr : r ∈ S k) :
      (k : ℝ)*ρ ≤ |t r - t s| ∧ |t r - t s| < (k + 1 : ℝ)*ρ := by
    have he := (Finset.mem_filter.mp hr).2
    change ⌊|t r - t s| / ρ⌋₊ = k at he
    exact ⟨(le_div_iff₀ hρ).mp (he ▸ Nat.floor_le (div_nonneg (abs_nonneg _) hρ.le)),
      (div_lt_iff₀ hρ).mp (he ▸ Nat.lt_floor_add_one _)⟩
  let M : ℝ := 2 * 11 ^ (d + 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcount (k) : ((S k).card : ℝ) ≤ M := by
    let pos := (S k).filter fun r => t s ≤ t r
    let neg := (S k).filter fun r => ¬ t s ≤ t r
    have pack (H : Finset L) (z : ℝ) (hH : H ⊆ S k)
        (hz : ∀ r ∈ H, |t r - z| ≤ ρ) : (H.card : ℝ) ≤ 11 ^ (d + 2) := by
      apply shell_packing H (p b) (v b) (hu b) center t z ρ hρ
        (fun r hr => hclose r (memJ (hH hr))) _ hz
      intro i hi j hj hij
      by_contra! h
      exact Set.disjoint_left.mp (hball i (memJ (hH hi)) j (memJ (hH hj)) hij)
        (Metric.mem_ball_self hρ) (Metric.mem_ball.mpr h)
    have hp := pack pos (t s + k * ρ) (Finset.filter_subset _ _) (by
      intro r hr
      obtain ⟨hm, ht⟩ := Finset.mem_filter.mp hr
      obtain ⟨lo, hi⟩ := bounds hm
      rw [abs_of_nonneg (sub_nonneg.mpr ht)] at lo hi
      apply abs_le.mpr; constructor <;> linarith)
    have hn := pack neg (t s - k * ρ) (Finset.filter_subset _ _) (by
      intro r hr
      obtain ⟨hm, ht⟩ := Finset.mem_filter.mp hr
      obtain ⟨lo, hi⟩ := bounds hm
      rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge ht))] at lo hi
      apply abs_le.mpr; constructor <;> linarith)
    have he : pos.card + neg.card = (S k).card := Finset.card_filter_add_card_filter_not ..
    dsimp [M]
    rw [← he, Nat.cast_add]
    linarith
  let w := fun k : ℕ => ((k : ℝ) ^ (d + 1))⁻¹
  let D := 2 * (257 : ℝ) ^ (d + 1) * (ρ ^ (d + 1))⁻¹
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hw (k) : 0 ≤ w k := by dsimp [w]; positivity
  have per (k) : ∑ r ∈ S k, f r ≤ M *
      ((if k ∈ Finset.range 128 then ((I s).card : ℝ) else 0) + D * w k) := by
    let weight := (if k ∈ Finset.range 128 then ((I s).card : ℝ) else 0) + D * w k
    have hweight : 0 ≤ weight := by dsimp [weight]; split <;> positivity
    calc
      _ ≤ ∑ _r ∈ S k, weight := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hk : k ∈ Finset.range 128
        · simp only [weight, ite_eq_left hk]
          exact le_add_of_le_of_nonneg
            (by
              dsimp [f]
              exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : I r ∩ I s ⊆ I s))
            (mul_nonneg hD (hw k))
        · simp only [weight, ite_eq_right hk, zero_add]
          apply far_overlap p v b δ ρ hδ hδρ hu hsep P r s (t r) (t s)
            (hpoints r (memJ hr)) (hpoints s hs) k (by simpa using hk) (bounds hr).1
          have h1 := abs_sub_le (t r) 0 (t s)
          simp at h1
          linarith [hlen r, hlen s]
      _ = ((S k).card : ℝ) * weight := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcount k) hweight
  have hsum : ∑ k ∈ K, w k ≤ ∑' k, w k :=
    (Real.summable_nat_pow_inv.mpr (show 1 < d + 1 by omega)).sum_le_tsum K (fun k _ => hw k)
  have hnear : ∑ k ∈ K, (if k ∈ Finset.range 128 then ((I s).card : ℝ) else 0) ≤
      128 * (I s).card := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ _k ∈ Finset.range 128, ((I s).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun _ h => (Finset.mem_filter.mp h).2)
          (by intros; positivity)
      _ = _ := by simp
  have hseries : 0 ≤ ∑' k, w k := tsum_nonneg hw
  calc
    _ = ∑ k ∈ K, ∑ r ∈ S k, f r := (Finset.sum_fiberwise_of_maps_to
      (fun r hr => Finset.mem_image_of_mem bin hr : (A : Set L).MapsTo bin K) f).symm
    _ ≤ _ := Finset.sum_le_sum (fun k _ => per k)
    _ = M * ((∑ k ∈ K, if k ∈ Finset.range 128 then ((I s).card : ℝ) else 0) +
        D * ∑ k ∈ K, w k) := by rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M * (128 * (I s).card + D * ∑' k, w k) := by gcongr
    _ ≤ _ := by
      change _ ≤ M * (128 + 2 * 257 ^ (d + 1) * ∑' k, w k) *
        (((I s).card : ℝ) + (ρ ^ (d + 1))⁻¹)
      dsimp only [D]
      have h1 : 0 ≤ M * 128 * (ρ ^ (d + 1))⁻¹ := by positivity
      have h2 : 0 ≤ M * (2 * 257 ^ (d + 1)) * (∑' k, w k) * ((I s).card : ℝ) := by positivity
      linarith only [h1, h2]

open Kakeya.Eighty4

theorem fixed_parent_overlap_dyadic {d : ℕ} (hd : 1 ≤ d)
    {T L : Type*} [Fintype T] [DecidableEq L]
    (p v : T → Space (d + 2)) (b : T) (δ ρ C : ℝ)
    (m : DyadicIndex (Fintype.card T))
    (hscale : ρ = C * (dyadicScale (Fintype.card T) m) ^ (-(1 : ℝ) / (d + 1)))
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hu : ∀ i, ‖v i‖ = 1) (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    (J : Finset L) (center : L → Space (d + 2)) (P : L → Set (Space (d + 2)))
    (hball : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      Disjoint (Metric.ball (center i) ρ) (Metric.ball (center j) ρ))
    (hne : ∀ r ∈ J, (P r).Nonempty)
    (hP : ∀ r ∈ J, P r ⊆ (unitTube (p b) (v b) δ ∩ Metric.ball (center r) (3 * ρ)) ∩
      concreteDyadicBand (fun i => unitTube (p i) (v i) δ) m)
    (s : L) (hs : s ∈ J) :
    let I := incidence (fun i => unitTube (p i) (v i) δ) P
    ∑ r ∈ J.erase s, ((I r ∩ I s).card : ℝ) ≤
      dyadicOverlapConstant d C * (I s).card := by
  classical
  let tube := fun i => unitTube (p i) (v i) δ
  let q := dyadicScale (Fintype.card T) m
  have hq : 0 < q := dyadicScale_pos _ _
  obtain ⟨x, hx⟩ := hne s hs
  have hband := (hP s hs hx).2.1
  change q ≤ tubeMultiplicity tube x at hband
  rw [tubeMultiplicity_eq_count] at hband
  have hsub : (Finset.univ.filter fun i => x ∈ tube i) ⊆ incidence tube P s := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, (Finset.mem_filter.mp hi).2, hx⟩
  have hlow : q ≤ ((incidence tube P s).card : ℝ) :=
    hband.trans (by exact_mod_cast Finset.card_le_card hsub)
  have hsize : (ρ ^ (d + 1))⁻¹ = (C ^ (d + 1))⁻¹ * q := by
    change ρ = C * q ^ (-(1 : ℝ) / (d + 1)) at hscale
    rw [hscale, mul_pow, ← Real.rpow_mul_natCast hq.le]
    have he : (-(1 : ℝ) / (d + 1)) * ((d + 1:ℕ) : ℝ) = -1 := by
      push_cast; field_simp
    rw [he, Real.rpow_neg_one, mul_inv, inv_inv]
  have hC : 0 < C := pos_of_mul_pos_left (hscale ▸ hδ.trans_le hδρ)
    (Real.rpow_nonneg hq.le _)
  apply (fixed_parent_overlap hd p v b δ ρ hδ hδρ hρ1 hu hsep J center P hball hne
    (fun r hr x hx => (hP r hr hx).1) s hs).trans
  rw [dyadicOverlapConstant, hsize, mul_assoc, add_mul, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left hlow (by positivity)) _) (overlapConstant_nonneg d)

end

def OrderedOverlapBound {T L : Type*} [DecidableEq T] [LinearOrder L]
    (K : ℝ) (B : Finset T) (R : Finset L) (parent : L → T) (I : L → Finset T) : Prop :=
  (∑ c ∈ B, ∑ i ∈ R.filter (fun r => parent r = c),
    ∑ j ∈ R.filter (fun j => i < j), ((I i ∩ I j).card : ℝ)) ≤
    K * ∑ c ∈ B, ∑ i ∈ R.filter (fun r => parent r = c), ((I i).card : ℝ)

def Lemma48Application {T L : Type*} [DecidableEq T] [LinearOrder L]
    (d : ℕ) (C : ℝ) (B : Finset T) (R : Finset L) (parent : L → T) (I : L → Finset T) : Prop :=
  OrderedOverlapBound (dyadicOverlapConstant d C) B R parent I

theorem incidence_sum_of_ordered_overlap {T L : Type*} [Fintype T] [DecidableEq T]
    [LinearOrder L] (K : ℝ≥0) (B : Finset T) (R : Finset L) (parent : L → T)
    (hparent : (R : Set L).MapsTo parent B) (I : L → Finset T)
    (happ : OrderedOverlapBound K B R parent I) :
    ∑ i ∈ R, ((I i).card : ℝ) ≤ (1 + 2 * (K : ℝ)) * Fintype.card T := by
  classical
  let a (i : L) (ℓ : T) : ℝ := if ℓ ∈ I i then 1 else 0
  let w (i j : L) := ((I i ∩ I j).card : ℝ)
  let upper (i j : L) := if i < j then w i j else 0
  let mass := ∑ i ∈ R, ((I i).card : ℝ)
  let pairs := ∑ i ∈ R, ∑ j ∈ R, upper i j
  have ha (i) : ∑ ℓ, a i ℓ = ((I i).card : ℝ) := by simp [a]
  have hw (i j) : ∑ ℓ, a i ℓ * a j ℓ = w i j := by
    calc
      _ = ∑ ℓ : T, if ℓ ∈ I i ∩ I j then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro ℓ _
        by_cases hi : ℓ ∈ I i <;> by_cases hj : ℓ ∈ I j <;> simp [a, hi, hj]
      _ = _ := by simp [w, -Finset.mem_inter]
  have hpair : pairs ≤ (K : ℝ) * mass := by
    unfold OrderedOverlapBound at happ
    rw [Finset.sum_fiberwise_of_maps_to hparent, Finset.sum_fiberwise_of_maps_to hparent] at happ
    simpa only [pairs, upper, mass, w, Finset.sum_filter] using happ
  have hsplit (i j) : w i j = (if i = j then ((I i).card : ℝ) else 0) +
      upper i j + upper j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · simp [upper, h, h.ne, not_lt_of_gt h]
    · simp [upper, w]
    · simp [upper, w, h, h.ne', not_lt_of_gt h, Finset.inter_comm]
  have hsw : (∑ i ∈ R, ∑ j ∈ R, upper j i) = pairs := Finset.sum_comm
  have hall : ∑ i ∈ R, ∑ j ∈ R, w i j = mass + 2 * pairs := by
    simp_rw [hsplit, Finset.sum_add_distrib]
    rw [hsw]
    have hdiag (i) (hi : i ∈ R) :
        (∑ j ∈ R, if i = j then ((I i).card : ℝ) else 0) = (I i).card := by simp [hi]
    rw [Finset.sum_congr rfl hdiag]
    change mass + pairs + pairs = _
    ring
  let degree (ℓ : T) := ∑ i ∈ R, a i ℓ
  have hmass : ∑ ℓ, degree ℓ = mass := by
    unfold degree; rw [Finset.sum_comm]; simp only [ha, mass]
  have hsquare : ∑ ℓ, (degree ℓ) ^ 2 = mass + 2 * pairs := by
    rw [← hall]
    unfold degree
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hw i j)
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset T)) (f := degree)
  rw [hmass, hsquare, Finset.card_univ] at hcs
  change mass ≤ _
  by_cases hm : mass = 0
  · have hK : 0 ≤ (K : ℝ) :=
      K.coe_nonneg
    rw [hm]; positivity
  · have hpos : 0 < mass :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Ne.symm hm)
    apply le_of_mul_le_mul_right ?_ hpos
    nlinarith [mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (Fintype.card T) : (0 : ℝ) ≤ _)]

theorem incidence_sum_of_lemma48_application {T L : Type*} [Fintype T] [DecidableEq T]
    [LinearOrder L] (d : ℕ) (C : ℝ≥0) (B : Finset T) (R : Finset L) (parent : L → T)
    (hparent : (R : Set L).MapsTo parent B) (I : L → Finset T)
    (happ : Lemma48Application d C B R parent I) :
    ∑ i ∈ R, ((I i).card : ℝ) ≤ (1 + 2 * dyadicOverlapConstant d C) * Fintype.card T := by
  let K : ℝ≥0 := ⟨dyadicOverlapConstant d C,
    mul_nonneg (overlapConstant_nonneg d) (by positivity)⟩
  exact incidence_sum_of_ordered_overlap K B R parent hparent I happ

end Kakeya.Ninety109
