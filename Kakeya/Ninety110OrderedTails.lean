module

public import Kakeya.Ninety110MultipleIncidences

@[expose] public section

namespace Kakeya.Ninety109

open scoped NNReal
variable {T L : Type*} [DecidableEq T] [LinearOrder L]

def orderedTail (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ) : Finset T :=
  (I i).filter fun l => k ≤ (R.filter fun j => i ≤ j ∧ l ∈ I j).card

def laterPieceIncidences (R : Finset L) (I : L → Finset T) (i : L) (ℓ : T) : Finset L :=
  R.filter fun j => i ≤ j ∧ ℓ ∈ I j

theorem orderedTail_subset_geometricHits {B : Type*} [Fintype T]
    (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ)
    (S : T → Finset B)
    (hcount : ∀ ℓ ∈ I i, (laterPieceIncidences R I i ℓ).card ≤ (S ℓ).card) :
    orderedTail R I i k ⊆ Finset.univ.filter (fun ℓ => k ≤ (S ℓ).card) := by
  classical
  intro ℓ hℓ
  obtain ⟨hi, hk⟩ := Finset.mem_filter.mp hℓ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.trans (hcount ℓ hi)⟩

theorem orderedTail_card_le_geometricHits {B : Type*} [Fintype T]
    (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ)
    (S : T → Finset B)
    (hcount : ∀ ℓ ∈ I i, (laterPieceIncidences R I i ℓ).card ≤ (S ℓ).card) :
    ((orderedTail R I i k).card : ℝ) ≤
      ((Finset.univ.filter (fun ℓ => k ≤ (S ℓ).card)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (orderedTail_subset_geometricHits R I i k S hcount)

theorem orderedTail_eq_inter_selection2 [Fintype T]
    (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ) :
    orderedTail R I i k = I i ∩
      Finset.univ.filter (fun ℓ => k ≤ (laterPieceIncidences R I i ℓ).card) := by
  classical
  ext ℓ
  constructor
  · intro h
    obtain ⟨hi, hk⟩ := Finset.mem_filter.mp h
    exact Finset.mem_inter.mpr
      ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  · intro h
    obtain ⟨hi, hs⟩ := Finset.mem_inter.mp h
    exact Finset.mem_filter.mpr
      ⟨hi, (Finset.mem_filter.mp hs).2⟩

theorem orderedTail_subset_laterIncidences [Fintype T]
    (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ) :
    orderedTail R I i k ⊆
      Finset.univ.filter (fun ℓ => k ≤ (laterPieceIncidences R I i ℓ).card) := by
  rw [orderedTail_eq_inter_selection2]
  intro ℓ hℓ
  exact (Finset.mem_inter.mp hℓ).2

theorem orderedTail_card_le_selection2 [Fintype T]
    (R : Finset L) (I : L → Finset T) (i : L) (k : ℕ) :
    ((orderedTail R I i k).card : ℝ) ≤
      ((Finset.univ.filter (fun ℓ => k ≤ (laterPieceIncidences R I i ℓ).card)).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (orderedTail_subset_laterIncidences R I i k)

theorem ordered_overlap_eq_sum_tails (R : Finset L) (I : L → Finset T) {i : L} (hi : i ∈ R) :
    ∑ j ∈ R.filter (fun j => i < j), (I i ∩ I j).card =
      ∑ k ∈ Finset.Icc 2 R.card, (orderedTail R I i k).card := by
  classical
  let later := R.filter (fun j => i < j)
  have inter (j) : I i ∩ I j = (I i).filter (fun l => l ∈ I j) := by ext; simp
  simp_rw [inter, Finset.card_filter]
  rw [Finset.sum_comm]
  unfold orderedTail
  simp_rw [Finset.card_filter (fun l => _ ≤ _) (I i)]
  rw [Finset.sum_comm (s := Finset.Icc 2 R.card)]
  apply Finset.sum_congr rfl
  intro l hl
  let D := R.filter fun j => i ≤ j ∧ l ∈ I j
  have he : D = insert i (later.filter fun j => l ∈ I j) := by
    ext j
    simp only [D, later, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hij, hlj⟩
      rcases hij.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨⟨hj, h⟩, hlj⟩
    · rintro (rfl | ⟨⟨hj, hij⟩, hlj⟩)
      · exact ⟨hi, le_rfl, hl⟩
      · exact ⟨hj, hij.le, hlj⟩
  have hcount : D.card = (later.filter fun j => l ∈ I j).card + 1 := by
    rw [he, Finset.card_insert_of_notMem]; simp [later]
  have hsub : D.card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hlevels : (Finset.Icc 2 R.card).filter (fun k => k ≤ D.card) = Finset.Icc 2 D.card := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  change (∑ j ∈ later, if l ∈ I j then 1 else 0) = ∑ k ∈ Finset.Icc 2 R.card,
    if k ≤ D.card then 1 else 0
  rw [← Finset.card_filter, ← Finset.card_filter, hlevels, Nat.card_Icc]
  omega

def OrderedTailApplication (d : ℕ) (K q : ℝ) (R : Finset L) (I : L → Finset T) : Prop :=
  ∀ i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
    ((orderedTail R I i k).card : ℝ) ≤ K * q * ((k : ℝ) ^ (d + 1))⁻¹

-- The ordered-tail estimate is stated as the two inequalities of the application.
def OrderedTailChainApplication [Fintype T]
    (d : ℕ) (K q : ℝ) (R : Finset L) (I : L → Finset T) : Prop :=
  ∀ i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
    ((orderedTail R I i k).card : ℝ) ≤
      ((Finset.univ.filter (fun ℓ : T =>
        k ≤ (laterPieceIncidences R I i ℓ).card)).card : ℝ) ∧
    ((Finset.univ.filter (fun ℓ : T =>
      k ≤ (laterPieceIncidences R I i ℓ).card)).card : ℝ) ≤
      K * q * ((k : ℝ) ^ (d + 1))⁻¹

theorem orderedTailApplication_of_tail_chain {d : ℕ} [Fintype T]
    (K q : ℝ) (R : Finset L) (I : L → Finset T)
    (hchain : OrderedTailChainApplication d K q R I) :
    OrderedTailApplication d K q R I := by
  intro i hi k hk
  exact (hchain i hi k hk).1.trans (hchain i hi k hk).2

theorem orderedTailApplication_of_selection2 {d : ℕ} [Fintype T]
    (K q : ℝ) (R : Finset L) (I : L → Finset T)
    (hselection2 : ∀ i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
      ((Finset.univ.filter (fun ℓ : T =>
        k ≤ (laterPieceIncidences R I i ℓ).card)).card : ℝ) ≤
        K * q * ((k : ℝ) ^ (d + 1))⁻¹) :
    OrderedTailApplication d K q R I := by
  intro i hi k hk
  exact (orderedTail_card_le_selection2 R I i k).trans (hselection2 i hi k hk)

theorem orderedTailApplication_of_geometric_bound {d : ℕ} [Fintype T]
    (K q : ℝ) (R : Finset L) (I : L → Finset T)
    (S : L → T → Finset L)
    (hcount : ∀ i ∈ R, ∀ ℓ ∈ I i,
      (laterPieceIncidences R I i ℓ).card ≤ (S i ℓ).card)
    (hgeometric : ∀ i ∈ R, ∀ k : ℕ, multipleThreshold d ≤ k →
      ((Finset.univ.filter (fun ℓ : T => k ≤ (S i ℓ).card)).card : ℝ) ≤
        K * q * ((k : ℝ) ^ (d + 1))⁻¹) :
    OrderedTailApplication d K q R I := by
  intro i hi k hk
  exact (orderedTail_card_le_geometricHits R I i k (S i) (hcount i hi)).trans
    (hgeometric i hi k hk)

section FixedTubeTail
attribute [local instance] Classical.propDecidable

theorem ordered_tail_card_of_fixed_tube_vitali_ball_tail {d : ℕ} [Fintype T]
    (p v : T → Space (d + 2)) (t : T) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hu : ∀ ℓ, ‖v ℓ‖ = 1)
    (hsep : ∀ ℓ s, ℓ ≠ s → δ ≤ dist (v ℓ) (v s))
    (R : Finset L) (I : L → Finset T) (i : L)
    (J : Finset L) (center : L → Space (d + 2))
    (hball : ∀ r ∈ J, ∀ s ∈ J, r ≠ s →
      Disjoint (Metric.ball (center r) ρ) (Metric.ball (center s) ρ))
    {k : ℕ} (hk : multipleThreshold d ≤ k)
    (C q : ℝ) (hq : 0 < q)
    (hscale : ρ = C * q ^ (-(1 : ℝ) / (d + 1)))
    (hcount : ∀ ℓ ∈ I i, (laterPieceIncidences R I i ℓ).card ≤
      (J.filter fun b =>
        (unitTube (p ℓ) (v ℓ) δ ∩ unitTube (p t) (v t) δ ∩
          Metric.ball (center b) (3 * ρ)).Nonempty).card) :
    ((orderedTail R I i k).card : ℝ) ≤
      (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * (C ^ (d + 1))⁻¹) *
        q * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  let S := fun ℓ : T => J.filter fun b =>
    (unitTube (p ℓ) (v ℓ) δ ∩ unitTube (p t) (v t) δ ∩
      Metric.ball (center b) (3 * ρ)).Nonempty
  calc
    ((orderedTail R I i k).card : ℝ) ≤
        ((Finset.univ.filter (fun ℓ => k ≤ (S ℓ).card)).card : ℝ) :=
      orderedTail_card_le_geometricHits R I i k S hcount
    _ ≤ _ := fixed_tube_vitali_ball_tail p v t δ ρ hδ hδρ hu hsep
      J center hball hk C q hq hscale

end FixedTubeTail

theorem ordered_tail_card_of_forward_ball_hits {d : ℕ} {B : Type*}
    [Finite T]
    (p v : T → Space (d + 2)) (t : T) (δ ρ : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hu : ∀ ℓ, ‖v ℓ‖ = 1)
    (hsep : ∀ ℓ s, ℓ ≠ s → δ ≤ dist (v ℓ) (v s))
    (R : Finset L) (I : L → Finset T) (i : L)
    (J : Finset B) (center : B → Space (d + 2)) (ballOf : L → B)
    (hball : ∀ r ∈ J, ∀ s ∈ J, r ≠ s →
      Disjoint (Metric.ball (center r) ρ) (Metric.ball (center s) ρ))
    (hforward : ∀ ℓ ∈ I i, ∀ j ∈ laterPieceIncidences R I i ℓ,
      ballOf j ∈ J ∧
        (unitTube (p ℓ) (v ℓ) δ ∩ unitTube (p t) (v t) δ ∩
          Metric.ball (center (ballOf j)) (3 * ρ)).Nonempty)
    (hinj : ∀ j ∈ R, ∀ j' ∈ R, ballOf j = ballOf j' → j = j')
    {k : ℕ} (hk : multipleThreshold d ≤ k)
    (C q : ℝ) (hq : 0 < q)
    (hscale : ρ = C * q ^ (-(1 : ℝ) / (d + 1))) :
    ((orderedTail R I i k).card : ℝ) ≤
      (2 * (258 * (binCapacity d : ℝ)) ^ (d + 1) * (C ^ (d + 1))⁻¹) *
        q * ((k : ℝ) ^ (d + 1))⁻¹ := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let S := fun ℓ : T => J.filter fun b =>
    (unitTube (p ℓ) (v ℓ) δ ∩ unitTube (p t) (v t) δ ∩
      Metric.ball (center b) (3 * ρ)).Nonempty
  have hcount : ∀ ℓ ∈ I i,
      (laterPieceIncidences R I i ℓ).card ≤ (S ℓ).card := by
    intro ℓ hℓ
    apply Finset.card_le_card_of_injOn ballOf
    · intro j hj
      exact Finset.mem_filter.mpr (hforward ℓ hℓ j hj)
    · intro j hj j' hj' he
      exact hinj j (Finset.mem_filter.mp hj).1
        j' (Finset.mem_filter.mp hj').1 he
  calc
    ((orderedTail R I i k).card : ℝ) ≤
        ((Finset.univ.filter fun ℓ : T => k ≤ (S ℓ).card).card : ℝ) :=
      orderedTail_card_le_geometricHits R I i k S hcount
    _ ≤ _ := fixed_tube_vitali_ball_tail p v t δ ρ hδ hδρ hu hsep
      J center hball hk C q hq hscale

noncomputable def tailOverlapConstant (d : ℕ) (K : ℝ≥0) : ℝ≥0 :=
  ⟨multipleThreshold d + (K : ℝ) * ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹, by
    have : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹ :=
      tsum_nonneg (fun k : ℕ => by positivity)
    positivity⟩

theorem ordered_overlap_of_tails {d : ℕ} (hd : 1 ≤ d) (K : ℝ≥0) (q : ℝ)
    (B : Finset T) (R : Finset L) (parent : L → T) (I : L → Finset T)
    (hlow : ∀ i ∈ R, q ≤ (I i).card) (h : OrderedTailApplication d K q R I) :
    OrderedOverlapBound (tailOverlapConstant d K) B R parent I := by
  classical
  unfold OrderedOverlapBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hir := (Finset.mem_filter.mp hi).1
  have he := congrArg (fun z : ℕ => (z : ℝ)) (ordered_overlap_eq_sum_tails R I hir)
  push_cast at he
  rw [he]
  let levels := Finset.Icc 2 R.card
  let w := fun k : ℕ => ((k : ℝ) ^ (d + 1))⁻¹
  have hw (k) : 0 ≤ w k := by dsimp [w]; positivity
  let n := ((I i).card : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have per (k : ℕ) : ((orderedTail R I i k).card : ℝ) ≤
      (if k ∈ Finset.range (multipleThreshold d) then n else 0) + (K * n) * w k := by
    split_ifs with hk
    · exact le_add_of_le_of_nonneg (by
        dsimp only [n]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _ : orderedTail R I i k ⊆ I i))
        (mul_nonneg (mul_nonneg K.coe_nonneg hn) (hw k))
    · rw [zero_add]
      apply (h i hir k (by simpa using hk)).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlow i hir) K.coe_nonneg) (hw k)
  have hnear : (∑ k ∈ levels, if k ∈ Finset.range (multipleThreshold d) then n else 0) ≤
      multipleThreshold d * n := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ _k ∈ Finset.range (multipleThreshold d), n :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun _ hk => (Finset.mem_filter.mp hk).2)
          (fun _ _ _ => hn)
      _ = _ := by simp
  have hs := (Real.summable_nat_pow_inv.mpr (show 1 < d + 1 by omega)).sum_le_tsum levels
    (fun k _ => hw k)
  have H := Finset.sum_le_sum (s := levels) (fun k _ => per k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at H
  apply H.trans
  change _ ≤ (multipleThreshold d + (K : ℝ) * ∑' k, w k) * n
  linarith only [hnear, mul_le_mul_of_nonneg_left hs (mul_nonneg K.coe_nonneg hn)]

end Kakeya.Ninety109
