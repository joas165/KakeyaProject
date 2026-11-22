module

public import Kakeya.Ninety109FixedParentOverlap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

namespace Kakeya.Ninety109

open Kakeya.Ninety21
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def binCapacity (d : ℕ) := 11 ^ (d + 2)
def multipleThreshold (d : ℕ) := 128 * binCapacity d

noncomputable def multipleHits {X T L : Type*} [Fintype T]
    (tube : T → Set X) (i : T) (ball : L → Set X) (J : Finset L) (k : ℕ) : Finset T :=
  Finset.univ.filter fun l => k ≤ (J.filter fun j => (tube l ∩ tube i ∩ ball j).Nonempty).card

theorem multiple_hits_concentration {d : ℕ} {T L : Type*} [Fintype T]
    (p v : T → Space (d + 2)) (i : T) (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hu : ∀ l, ‖v l‖ = 1) (J : Finset L) (center : L → Space (d + 2))
    (hball : ∀ r ∈ J, ∀ s ∈ J, r ≠ s →
      Disjoint (Metric.ball (center r) ρ) (Metric.ball (center s) ρ))
    {k : ℕ} (hk : multipleThreshold d ≤ k) {l : T}
    (hl : l ∈ multipleHits (fun a => unitTube (p a) (v a) δ) i
      (fun j => Metric.ball (center j) (3 * ρ)) J k) :
    k * ρ ≤ 2 * binCapacity d ∧
      ¬ TransverseDirections (v i) (v l) (64 * binCapacity d * δ / (k * ρ)) := by
  classical
  let S := J.filter fun j => ((unitTube (p l) (v l) δ ∩ unitTube (p i) (v i) δ) ∩
    Metric.ball (center j) (3 * ρ)).Nonempty
  have hcard : k ≤ S.card := (Finset.mem_filter.mp hl).2
  let M := binCapacity d
  have hM : 0 < M := by dsimp [M, binCapacity]; positivity
  have hk' : 128 * M ≤ k := hk
  have hkpos : 0 < k := by omega
  have hρ := hδ.trans_le hδρ
  have hne : S.Nonempty := Finset.card_pos.mp (hkpos.trans_le hcard)
  have witnesses (j) : ∃ t : ℝ, |t| ≤ 1/2 ∧
      (j ∈ S → dist (center j) (p i + t • v i) ≤ 4 * ρ) := by
    by_cases hj : j ∈ S
    · obtain ⟨x, hx, hb⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨t, ht, ht'⟩ := originalTube_ball_center_near_axis _ _ _ δ (3 * ρ) ⟨x, hb, hx.2⟩
      exact ⟨t, ht, fun _ => by linarith⟩
    · exact ⟨0, by norm_num, by simp [hj]⟩
  choose t ht hclose using witnesses
  obtain ⟨a, ha, hmin⟩ := S.exists_max_image (fun j => -t j) hne
  obtain ⟨b, hb, hmax⟩ := S.exists_max_image t hne
  let bin := fun j => ⌊(t j - t a) / ρ⌋₊
  let bins := Finset.range (bin b + 1)
  have lower (j) (hj : j ∈ S) : 0 ≤ t j - t a := by linarith [hmin j hj]
  have maps : (S : Set L).MapsTo bin bins := by
    intro j hj
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_mono (by gcongr; exact hmax j hj))
  have per (z : ℕ) : (((S.filter fun j => bin j = z).card : ℕ) : ℝ) ≤ M := by
    simp only [M, binCapacity, Nat.cast_pow, Nat.cast_ofNat]
    apply shell_packing (S.filter fun j => bin j = z) (p i) (v i) (hu i) center t
      (t a + z * ρ) ρ hρ (fun j hj => hclose j (Finset.mem_filter.mp hj).1)
    · intro r hr s hs hrs
      have mem (j) (hj : j ∈ S.filter fun j => bin j = z) : j ∈ J :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      by_contra! h
      exact Set.disjoint_left.mp (hball r (mem r hr) s (mem s hs) hrs)
        (Metric.mem_ball_self hρ) (Metric.mem_ball.mpr h)
    · intro j hj
      obtain ⟨hs, hz⟩ := Finset.mem_filter.mp hj
      have lo := (le_div_iff₀ hρ).mp (Nat.floor_le (div_nonneg (lower j hs) hρ.le))
      have hi := (div_lt_iff₀ hρ).mp (Nat.lt_floor_add_one ((t j - t a) / ρ))
      change ⌊(t j - t a) / ρ⌋₊ = z at hz
      rw [hz] at lo hi
      apply abs_le.mpr
      constructor <;> linarith
  have bound := Finset.sum_le_sum (s := bins) (fun z _ => per z)
  have fibers := Finset.sum_fiberwise_of_maps_to maps (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at fibers bound
  rw [fibers] at bound
  have hf := (le_div_iff₀ hρ).mp (Nat.floor_le (div_nonneg (lower b hb) hρ.le))
  change (bin b : ℝ) * ρ ≤ _ at hf
  have hkr : (k : ℝ) * ρ ≤ M * (t b - t a + ρ) := by
    have h := (show (k : ℝ) ≤ S.card by exact_mod_cast hcard).trans bound
    simp only [bins, Finset.card_range, Nat.cast_add, Nat.cast_one] at h
    nlinarith [mul_le_mul_of_nonneg_right h hρ.le,
      mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg M)]
  have hbig : 128 * (M : ℝ) ≤ k := by exact_mod_cast hk'
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hsmall : (M : ℝ) * ρ ≤ (k : ℝ) * ρ / 128 := by
    nlinarith [mul_le_mul_of_nonneg_right hbig hρ.le]
  constructor
  · change _ ≤ 2 * (M : ℝ)
    have hlen : t b - t a ≤ 1 := by linarith [(abs_le.mp (ht a)).1, (abs_le.mp (ht b)).2]
    nlinarith [mul_le_mul_of_nonneg_left hlen hMr.le]
  · intro htrans
    let θ := 64 * (M : ℝ) * δ / (k * ρ)
    have hθ : 0 < θ := by dsimp [θ]; positivity
    obtain ⟨x, hx, hxb⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨y, hy, hyb⟩ := (Finset.mem_filter.mp hb).2
    have hxy := two_transverse_tubes_ball_center_diameter (p i) (p l) (v i) (v l)
      x y δ δ θ hθ le_rfl (hu i) htrans
      ⟨x, Metric.mem_ball_self hδ, hx.2⟩ ⟨x, Metric.mem_ball_self hδ, hx.1⟩
      ⟨y, Metric.mem_ball_self hδ, hy.2⟩ ⟨y, Metric.mem_ball_self hδ, hy.1⟩
    have he : (M : ℝ) * ((4 + 8 / θ) * δ) = 4 * M * δ + k * ρ / 8 := by
      dsimp [θ]; field_simp; ring
    have hsep := dist_triangle (p i + t a • v i) x (p i + t b • v i)
    rw [axis_dist _ _ (hu i), abs_sub_comm, abs_of_nonneg (lower b hb), dist_comm _ x] at hsep
    have hspan : t b - t a ≤ 14 * ρ + (4 + 8 / θ) * δ := by
      linarith [dist_triangle x y (p i + t b • v i),
        dist_triangle x (center a) (p i + t a • v i),
        dist_triangle y (center b) (p i + t b • v i), Metric.mem_ball.mp hxb,
        Metric.mem_ball.mp hyb, hclose a ha, hclose b hb]
    nlinarith [mul_le_mul_of_nonneg_left hspan hMr.le,
      mul_le_mul_of_nonneg_left hδρ hMr.le, mul_pos hMr hρ]

open scoped InnerProductSpace

section

variable {d : ℕ} {T L : Type*} [Fintype T]
    (p v : T → Space (d + 2)) (i : T) (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hu : ∀ l, ‖v l‖ = 1) (hsep : ∀ l s, l ≠ s → δ ≤ dist (v l) (v s))
    (J : Finset L) (center : L → Space (d + 2))
    (hball : ∀ r ∈ J, ∀ s ∈ J, r ≠ s →
      Disjoint (Metric.ball (center r) ρ) (Metric.ball (center s) ρ))
    {k : ℕ} (hk : multipleThreshold d ≤ k)

include hδ hδρ hu hball hk in
theorem multiple_hits_angle {l : T}
    (hl : l ∈ multipleHits (fun a => unitTube (p a) (v a) δ) i
      (fun j => Metric.ball (center j) (3 * ρ)) J k) :
    Real.arccos |⟪v i, v l⟫_ℝ| ≤ (32 * Real.pi * binCapacity d) * δ / (k * ρ) := by
  have h := (multiple_hits_concentration p v i δ ρ hδ hδρ hu J center hball hk hl).2
  let θ := 64 * (binCapacity d : ℝ) * δ / (k * ρ)
  have hρ := hδ.trans_le hδρ
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hs := unit_sine_sq_lt_of_not_transverse _ _ (hu i) (hu l) θ hθ h
  let α := Real.arccos |⟪v i, v l⟫_ℝ|
  have hc : Real.cos α = |⟪v i, v l⟫_ℝ| := by
    apply Real.cos_arccos (by linarith [abs_nonneg ⟪v i, v l⟫_ℝ])
    simpa [hu] using abs_real_inner_le_norm (v i) (v l)
  have hid := Real.sin_sq_add_cos_sq α
  rw [hc, sq_abs] at hid
  have hs' : Real.sin α ≤ θ := by nlinarith
  have hα := Real.mul_le_sin (Real.arccos_nonneg _) (Real.arccos_le_pi_div_two.mpr
    (abs_nonneg ⟪v i, v l⟫_ℝ))
  have hh := hα.trans hs'
  rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at hh
  change α ≤ _
  dsimp only [θ] at hh
  change 2 * α ≤ _ at hh
  calc
    α ≤ (64 * binCapacity d * δ / (k * ρ) * Real.pi) / 2 := by linarith
    _ = _ := by ring

include hδ hδρ hu hsep hball hk in
theorem multiple_hits_card :
    ((multipleHits (fun a => unitTube (p a) (v a) δ) i
      (fun j => Metric.ball (center j) (3 * ρ)) J k).card : ℝ) ≤
      2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * ((k * ρ) ^ (d + 1))⁻¹ := by
  classical
  let H := multipleHits (fun a => unitTube (p a) (v a) δ) i
    (fun j => Metric.ball (center j) (3 * ρ)) J k
  change (H.card : ℝ) ≤ _
  rcases H.eq_empty_or_nonempty with h | ⟨l, hl⟩
  · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]
    have := hδ.trans_le hδρ
    positivity
  have hρ := hδ.trans_le hδρ
  let M := (binCapacity d : ℝ)
  have hM : 0 < M := by dsimp [M, binCapacity]; positivity
  have hk' : 128 * M ≤ k := by
    dsimp [M]; exact_mod_cast (show 128 * binCapacity d ≤ k from hk)
  have hkρ : 0 < (k : ℝ) * ρ := mul_pos (by linarith) hρ
  let θ := 64 * M * δ / (k * ρ)
  have hθ : 0 < θ := div_pos (by positivity) hkρ
  have half : θ ≤ 1 / 2 := by
    apply (div_le_iff₀ hkρ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hk' hρ.le, mul_le_mul_of_nonneg_left hδρ hM.le]
  have bound (j : T) (hj : j ∈ H) := multiple_hits_concentration p v i δ ρ hδ hδρ hu J center hball hk hj
  have sub : H ⊆ nonTransverseDirectionIndices v θ i := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (bound j hj).2⟩
  have hc := original_unit_directions_quantitative_cap_card v δ θ hδ hθ half hu hsep i
  have hscale := (bound l hl).1
  have hbase : 1 + 4 * θ / δ ≤ 258 * M / (k * ρ) := by
    dsimp only [θ]
    apply (le_div_iff₀ hkρ).mpr
    have hkpos : (0 : ℝ) < k := by linarith
    have he : (1 + 4 * (64 * M * δ / (k * ρ)) / δ) * (k * ρ) =
        k * ρ + 256 * M := by field_simp [hkpos.ne', hρ.ne', hδ.ne']; ring
    rw [he]
    change (k : ℝ) * ρ ≤ 2 * M at hscale
    linarith
  calc
    _ ≤ ((nonTransverseDirectionIndices v θ i).card : ℝ) := by exact_mod_cast Finset.card_le_card sub
    _ ≤ _ := hc
    _ ≤ 2 * (258 * M / (k * ρ)) ^ (d + 1) := by gcongr
    _ = _ := by rw [div_pow]; ring

include hδ hδρ hu hsep hball hk in
theorem multiple_hits_card_dyadic (C q : ℝ) (hq : 0 < q)
    (hscale : ρ = C * q ^ (-(1 : ℝ) / (d + 1))) :
    ((multipleHits (fun a => unitTube (p a) (v a) δ) i
      (fun j => Metric.ball (center j) (3 * ρ)) J k).card : ℝ) ≤
      (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * (C ^ (d + 1))⁻¹) *
        q * ((k : ℝ) ^ (d + 1))⁻¹ := by
  apply (multiple_hits_card p v i δ ρ hδ hδρ hu hsep J center hball hk).trans
  rw [mul_pow (k : ℝ) ρ, hscale, mul_pow C, ← Real.rpow_mul_natCast hq.le]
  have he : (-(1 : ℝ) / (d + 1)) * ((d + 1 : ℕ) : ℝ) = -1 := by push_cast; field_simp
  rw [he, Real.rpow_neg_one, mul_inv, mul_inv, inv_inv]
  exact le_of_eq (by ring)

include hδ hδρ hu hsep hball hk in
theorem fixed_tube_vitali_ball_tail (C q : ℝ) (hq : 0 < q)
    (hscale : ρ = C * q ^ (-(1 : ℝ) / (d + 1))) :
    let tube := fun a => unitTube (p a) (v a) δ
    ((Finset.univ.filter fun ℓ : T => k ≤
      (J.filter fun b => (tube ℓ ∩ tube i ∩ Metric.ball (center b) (3 * ρ)).Nonempty).card).card : ℝ)
      ≤ (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * (C ^ (d + 1))⁻¹) *
        q * ((k : ℝ) ^ (d + 1))⁻¹ := by
  exact multiple_hits_card_dyadic p v i δ ρ hδ hδρ hu hsep J center hball hk C q hq hscale

end

end Kakeya.Ninety109
