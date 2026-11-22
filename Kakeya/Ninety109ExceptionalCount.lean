module

public import Kakeya.Ninety109RetainedCover

@[expose] public section

namespace Kakeya.Ninety109

open MeasureTheory Kakeya.Eighty4 Kakeya.Ninety21
open scoped NNReal

private theorem exceptional_fiber_card {T L : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    [LinearOrder L] (d : ℕ) (A : ℝ≥0) (J : Finset L) (I : L → Finset T)
    (hrow : ∀ i ∈ J, ∑ j ∈ J.erase i, ((I j ∩ I i).card : ℝ) ≤
      dyadicOverlapConstant d A * (I i).card)
    (hexc : ∀ i ∈ J, Fintype.card T < 2 * (I i).card) :
    (J.card : ℝ) ≤ 2 * (1 + 2 * dyadicOverlapConstant d A) := by
  classical
  let b : T := Classical.arbitrary T
  have happ : Lemma48Application d A {b} J (fun _ => b) I := by
    simp only [Lemma48Application, OrderedOverlapBound, Finset.sum_singleton, eq_self,
      Finset.filter_true, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply le_trans _ (hrow i hi)
    simp_rw [Finset.inter_comm (I i)]
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
    intro j hj
    obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_erase.mpr ⟨ne_of_gt hij, hj⟩
  have hm := incidence_sum_of_lemma48_application d A {b} J (fun _ => b)
    (fun _ _ => Finset.mem_singleton_self _) I happ
  have hsum := Finset.sum_le_sum (fun i hi =>
    (show (Fintype.card T : ℝ) ≤ 2 * (I i).card by exact_mod_cast (hexc i hi).le))
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  apply le_of_mul_le_mul_right _ (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < Fintype.card T)
  linarith

variable {T : Type*} [Fintype T] [Nonempty T] {d : ℕ}
    {p u : T → Space (d + 2)} {δ : ℝ}
    {g : ConcreteTubeBallGeometry (fun i => unitTube (p i) (u i) δ)}
    (v : ConcreteGreedyVitaliCandidates _ g)
    (μ : Measure (Space (d + 2))) [IsFiniteMeasure μ]
    (b : ConcreteTubeBallBounds μ _ (d + 2) v.retained)
    (hv : CoverVolumeBound v μ b)

omit [IsFiniteMeasure μ] in
theorem exceptional_cover_count (hd : 1 ≤ d) (A : ℝ≥0) (hδ : 0 < δ)
    (hu : ∀ i, ‖u i‖ = 1) (hsep : ∀ i j, i ≠ j → δ ≤ dist (u i) (u j))
    (m : DyadicIndex (Fintype.card T)) (hδR : δ ≤ v.radius m) (hR : v.radius m ≤ 1)
    (hscale : v.radius m = A * dyadicScale (Fintype.card T) m ^ (-(1 : ℝ) / (d + 1))) :
    let s := coverData v μ b hv
    dyadicScale (Fintype.card T) m * (paperExceptionalPieces μ _ (d + 2) s m).card ≤
      4 * (1 + 2 * dyadicOverlapConstant d A) * Fintype.card T := by
  classical
  let s := coverData v μ b hv
  let Q := {i // i ∈ s.P m}
  let : LinearOrder Q := WellOrderingRel.isWellOrder.linearOrder
  let E := paperExceptionalPieces μ _ (d + 2) s m
  let J := fun j => E.filter fun i => s.parent m i = j
  let P := fun i : Q => coverPiece v m (Sum.inr i)
  let center := fun i : Q => v.centers m (v.retained.ballOf m (Sum.inr i))
  let I := incidence (fun i => unitTube (p i) (u i) δ) P
  have hcard (j) (hj : j ∈ s.B m) :
      ((J j).card : ℝ) ≤ 2 * (1 + 2 * dyadicOverlapConstant d A) := by
    have par {i} (hi : i ∈ J j) : v.retained.tubeOf m (Sum.inr i) = j :=
      (Finset.mem_filter.mp hi).2
    have hsel {i} (hi : i ∈ J j) : v.retained.ballOf m (Sum.inr i) ∈ v.selected m j :=
      v.parent_associated_mem_selected m j _ ⟨Sum.inr i, par hi, rfl⟩
    apply exceptional_fiber_card d A (J j) I
    · intro i hi
      have hf := fixed_parent_overlap_dyadic hd p u j δ (v.radius m) A m hscale
        hδ hδR hR hu hsep (J j) center P (by
        intro x hx y hy hxy
        have hneq : v.retained.ballOf m (Sum.inr x) ≠ v.retained.ballOf m (Sum.inr y) := by
          intro he
          apply hxy
          apply Subtype.ext
          exact Prod.ext ((par hx).trans (par hy).symm) (congrArg Fin.val he)
        have h := v.selected_disjoint m j
          (ConcreteGreedyVitaliCandidates.retained_parents_subset g v m hj)
          _ (hsel hx) _ (hsel hy) hneq
        exact (congrArg₂ (fun a b : Set (Space (d + 2)) => Disjoint a b)
          (v.hBall m (v.retained.ballOf m (Sum.inr x)))
          (v.hBall m (v.retained.ballOf m (Sum.inr y)))).mp h) (fun z _ => coverPiece_nonempty v m (Sum.inr z)) (by
        intro x hx z hz
        have hgain := hz.1
        exact ⟨⟨par hx ▸ v.retained.gain_subset_parentTube m _ hgain, hz.2⟩,
          v.retained.gain_subset_dyadicLevel m _ hgain⟩) i hi
      convert! hf using 2
      congr! 3
    · intro i hi
      have h := (mem_paperExceptionalPieces μ _ (d + 2) s m i).mp (Finset.mem_filter.mp hi).1
      change Fintype.card T < 2 * (Finset.univ.filter
        (fun t => (P i ∩ unitTube (p t) (u t) δ).Nonempty)).card at h
      change Fintype.card T < 2 * (Finset.univ.filter
        (fun t => (unitTube (p t) (u t) δ ∩ P i).Nonempty)).card
      simpa only [Set.inter_comm (P i)] using h
  have he := Finset.card_eq_sum_card_fiberwise
    (fun i _ => s.hParent m i : (E : Set Q).MapsTo (s.parent m) (s.B m))
  have hsum := Finset.sum_le_sum hcard
  have hreal : (E.card : ℝ) = ∑ j ∈ s.B m, ((J j).card : ℝ) := by exact_mod_cast he
  rw [← hreal, Finset.sum_const, nsmul_eq_mul] at hsum
  have hq := dyadicScale_pos (Fintype.card T) m
  have hK : 0 ≤ dyadicOverlapConstant d A := by
    unfold dyadicOverlapConstant overlapConstant
    have hseries : 0 ≤ ∑' k : ℕ, ((k : ℝ) ^ (d + 1))⁻¹ := tsum_nonneg fun _ => by positivity
    positivity
  have h1 := mul_le_mul_of_nonneg_left hsum hq.le
  have h2 := mul_le_mul_of_nonneg_right (s.hGreedy m)
    (show 0 ≤ 2 * (1 + 2 * dyadicOverlapConstant d A) by positivity)
  change dyadicScale _ m * (E.card : ℝ) ≤ _
  linarith

end Kakeya.Ninety109
