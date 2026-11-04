module
public import Mathlib
public import Kakeya.ConditionalKakeya
public import Kakeya.Eighty9RepresentativeIncidence
public import Kakeya.Eighty9LevelBudget
public import Kakeya.Eighty9TubeWiseVitaliReindexed

/-!
# Lower-incidence Kakeya completion

Reindexed small pieces, incidence lemmas, and level-budget consequences.
-/

@[expose] public section

open scoped BigOperators

namespace Kakeya.Eighty9

section ChosenPairs

variable {T I K X : Type*} [MetricSpace X]

variable [DecidableEq T] [DecidableEq I] [DecidableEq K]

def chosenSmallPiece
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I)
    (p : TubeWiseVitaliLabel B S) : Set X :=
  (((tube p.1.val ∩ gain p.1.val) ∩ F) ∩
    Metric.ball (b p.1.val p.2.val) R)

theorem chosen_fiber_nonempty_of_vitali_cover
    (L S : T → Finset I) (B : Finset T)
    (b : T → I → X) (R : ℝ)
    (hOriginal : ∀ j ∈ B, (L j).Nonempty)
    (hVitaliCover : ∀ j ∈ B, ∀ i ∈ L j, ∃ d ∈ S j,
      Metric.ball (b j i) R ⊆ Metric.ball (b j d) (3 * R)) :
    ∀ j ∈ B, (S j).Nonempty := by
  intro j hj
  obtain ⟨i, hi⟩ := hOriginal j hj
  obtain ⟨d, hd, _⟩ := hVitaliCover j hj i hi
  exact ⟨d, hd⟩

noncomputable def chosenRepresentative
    (B : Finset T) (S : T → Finset I)
    (hNonemptyFiber : ∀ j ∈ B, (S j).Nonempty) :
    {j : T // j ∈ B} → TubeWiseVitaliLabel B S := by
  classical
  intro j
  let h := hNonemptyFiber j.val j.property
  exact ⟨j, ⟨Classical.choose h, Classical.choose_spec h⟩⟩

@[simp] theorem chosenRepresentative_tube
    (B : Finset T) (S : T → Finset I)
    (hNonemptyFiber : ∀ j ∈ B, (S j).Nonempty)
    (j : {j : T // j ∈ B}) :
    (chosenRepresentative B S hNonemptyFiber j).1 = j := by
  rfl

def reindexedSmallPiece
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (k : {k : K // k ∈ D}) : Set X :=
  chosenSmallPiece tube gain F b R B S (e k)

private theorem chosen_label_ext
    (B : Finset T) (S : T → Finset I)
    (p p' : TubeWiseVitaliLabel B S)
    (hTube : p.1.val = p'.1.val)
    (hBall : p.2.val = p'.2.val) : p = p' := by
  cases p with
  | mk j i =>
    cases p' with
    | mk j' i' =>
      have hj : j = j' := Subtype.ext hTube
      subst j'
      have hi : i = i' := Subtype.ext hBall
      subst i'
      rfl

theorem chosenSmallPiece_pairwise_disjoint
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R)) :
    ∀ p p' : TubeWiseVitaliLabel B S, p ≠ p' →
      Disjoint (chosenSmallPiece tube gain F b R B S p)
        (chosenSmallPiece tube gain F b R B S p') := by
  intro p p' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  by_cases ht : p.1.val = p'.1.val
  · have hi : p.2.val ≠ p'.2.val := by
      intro heq
      exact hne (chosen_label_ext B S p p' ht heq)
    have hi' : p'.2.val ∈ S p.1.val := by
      simpa [ht] using p'.2.property
    have hxBall' : x ∈ Metric.ball (b p.1.val p'.2.val) R := by
      rw [ht]
      exact hx'.2
    exact (Set.disjoint_left.mp
      (hBalls p.1.val p.1.property p.2.val p.2.property
        p'.2.val hi' hi)) hx.2 hxBall'
  · exact (Set.disjoint_left.mp
      (hGain p.1.val p.1.property p'.1.val p'.1.property ht))
        hx.1.1.2 hx'.1.1.2

theorem reindexedSmallPiece_pairwise_disjoint
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R)) :
    ∀ k k' : {k : K // k ∈ D}, k ≠ k' →
      Disjoint (reindexedSmallPiece tube gain F b R B S D e k)
        (reindexedSmallPiece tube gain F b R B S D e k') := by
  intro k k' hne
  exact chosenSmallPiece_pairwise_disjoint
    tube gain F b R B S hGain hBalls (e k) (e k')
      (fun heq => hne (e.injective heq))

/-- Every indexed small piece is nonempty by the selected-piece input. -/
theorem reindexedSmallPiece_nonempty
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    ∀ k : {k : K // k ∈ D},
      (reindexedSmallPiece tube gain F b R B S D e k).Nonempty := by
  intro k
  exact hSelectedNonempty (e k).1.val (e k).1.property
    (e k).2.val (e k).2.property

/-- Injectivity of E is proved using the already established disjointness
and nonemptiness of the reindexed geometric pieces. -/
theorem reindexedSmallPiece_injective
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    Function.Injective (reindexedSmallPiece tube gain F b R B S D e) := by
  exact pieceMap_injective_of_disjoint_nonempty
    (reindexedSmallPiece tube gain F b R B S D e)
    (reindexedSmallPiece_pairwise_disjoint
      tube gain F b R B S D e hGain hBalls)
    (reindexedSmallPiece_nonempty
      tube gain F b R B S D e hSelectedNonempty)

/-- The actual D ↔ tube–ball equivalence provides range coverage if the
representative domain consists of ALL tube–ball labels. This is distinct
from coverage by one representative for each selected tube. -/
theorem composedIntoRange_surjective_of_pair_equiv
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (E : {k : K // k ∈ D} → Set X) :
    Function.Surjective (composedIntoRange E e.symm) := by
  exact composedIntoRange_surjective_of_bijective E e.symm e.symm.bijective

/-- User's injectivity route for the selected-tube representative map.
The piece map's injectivity is PROVED from the geometric inputs, while
range coverage of `E ∘ rep` must concern THIS specific `rep`. -/
theorem reindexed_lower_incidence_of_composed_range
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (rep : {j : T // j ∈ B} → {k : K // k ∈ D})
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hRange : Function.Surjective
      (composedIntoRange
        (reindexedSmallPiece tube gain F b R B S D e) rep)) :
    LowerIncidence
      (reindexedSmallPiece tube gain F b R B S D e) rep := by
  exact lowerIncidence_of_composed_injective
    (reindexedSmallPiece tube gain F b R B S D e) rep
    (reindexedSmallPiece_nonempty
      tube gain F b R B S D e hSelectedNonempty)
    (reindexedSmallPiece_injective
      tube gain F b R B S D e hGain hBalls hSelectedNonempty)
    hRange

/-- The injectivity route applied to the bijection k = e.symm:
(i) E is injective from disjointness and nonemptiness;
(ii) E ∘ k covers Set.range E because k is bijective;
(iii) k is surjective, so the canonical LowerIncidence holds.
No coverage hypothesis is added. -/
theorem reindexed_lower_incidence_of_pair_equiv_injective
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    LowerIncidence
      (reindexedSmallPiece tube gain F b R B S D e) e.symm := by
  let E := reindexedSmallPiece tube gain F b R B S D e
  have hInj : Function.Injective E :=
    reindexedSmallPiece_injective
      tube gain F b R B S D e hGain hBalls hSelectedNonempty
  have hSurj : Function.Surjective (composedIntoRange E e.symm) :=
    composedIntoRange_surjective_of_pair_equiv B S D e E
  exact lowerIncidence_of_composed_injective E e.symm
    (reindexedSmallPiece_nonempty
      tube gain F b R B S D e hSelectedNonempty)
    hInj hSurj

/-- The existing pair-label equivalence really does provide lower incidence,
when representatives range over ALL selected tube–ball pairs. The domain here
is `TubeWiseVitaliLabel B S`, not the selected tubes alone. -/
theorem reindexed_lower_incidence_of_pair_equiv
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    LowerIncidence
      (reindexedSmallPiece tube gain F b R B S D e) e.symm := by
  apply lowerIncidence_of_bijective
  · intro k
    exact hSelectedNonempty (e k).1.val (e k).1.property
      (e k).2.val (e k).2.property
  · exact e.symm.bijective


/-! ## Incidence with the ball index of each reindexed piece

This is the literal (tube, ball, gain)-intersection relation from the
manuscript.  The selected testing tube `r` is tested using the same ball
*index* `(e k).2.val` as the piece being counted, rather than one
chosen representative ball for all pieces of `r`.
-/

/-- The actual selected-tube/selected-ball incidence: the right-hand testing
piece uses the ball label belonging to `k`.  Both sides include their own
trimmed gains.  Unlike `representativeIncidence`, this is not defined by a
single map choosing one piece per tube. -/
def sameBallTubeIncidence
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (r : T) (k : {k : K // k ∈ D}) : Prop :=
  (reindexedSmallPiece tube gain F b R B S D e k ∩
    (((tube r ∩ gain r) ∩ F) ∩
      Metric.ball (b r (e k).2.val) R)).Nonempty

/-- The paper's lower-incidence count is unconditional given nonempty
selected pieces: for each k, choose r = (e k).1.val in B.  The two
intersected sets then agree exactly, so their intersection is nonempty.
This is the precise use of the bijective reindexing e (the map k). -/
theorem sameBallTubeIncidence_column_covered
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    ∀ k : {k : K // k ∈ D},
      ∃ r ∈ B, sameBallTubeIncidence tube gain F b R B S D e r k := by
  intro k
  let p : TubeWiseVitaliLabel B S := e k
  refine ⟨p.1.val, p.1.property, ?_⟩
  obtain ⟨x, hx⟩ :=
    hSelectedNonempty p.1.val p.1.property p.2.val p.2.property
  change (chosenSmallPiece tube gain F b R B S p ∩
    chosenSmallPiece tube gain F b R B S p).Nonempty
  exact ⟨x, hx, hx⟩

/-- The displayed count of selected tubes incident to each localized piece
is at least one. The witness is the original tube label of that piece. -/
theorem sameBallTubeIncidence_column_card_pos
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (k : {k : K // k ∈ D})
    [DecidablePred (fun r : T =>
      sameBallTubeIncidence tube gain F b R B S D e r k)] :
    1 ≤ (B.filter (fun r =>
      sameBallTubeIncidence tube gain F b R B S D e r k)).card := by
  classical
  obtain ⟨r, hr, hInc⟩ :=
    sameBallTubeIncidence_column_covered
      tube gain F b R B S D e hSelectedNonempty k
  have hMem : r ∈ B.filter (fun r =>
      sameBallTubeIncidence tube gain F b R B S D e r k) := by
    simp [hr, hInc]
  have hPos : 0 < (B.filter (fun r =>
      sameBallTubeIncidence tube gain F b R B S D e r k)).card :=
    Finset.card_pos.mpr ⟨r, hMem⟩
  omega

/-- The same incidence relation is used in the column and row sums.
The lower (column) condition was proved above; the row <= 1 condition
is stated separately because distinct Vitali balls for one tube may
produce multiple incidences in the SAME row. -/
theorem reindexed_card_le_of_same_ball_incidence
    [Fintype T]
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hRow : ∀ r ∈ B,
      Kakeya.Seventy7.weight
        (sameBallTubeIncidence tube gain F b R B S D e)
        (fun _ => 1) r ≤ 1) :
    (D.card : ℝ) ≤ (B.card : ℝ) := by
  classical
  have hCount : (Fintype.card {k : K // k ∈ D} : ℝ) ≤
      (B.card : ℝ) :=
    selected_incidence_double_count
      (sameBallTubeIncidence tube gain F b R B S D e)
      B
      (sameBallTubeIncidence_column_covered
        tube gain F b R B S D e hSelectedNonempty)
      hRow
  simpa using hCount

/-- The greedy numerical budget, with the manuscript's actual
same-ball incidence in place of a fixed representative map. -/
theorem reindexed_budget_of_same_ball_incidence
    [Fintype T]
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hRow : ∀ r ∈ B,
      Kakeya.Seventy7.weight
        (sameBallTubeIncidence tube gain F b R B S D e)
        (fun _ => 1) r ≤ 1)
    (q N : ℝ) (hq : 0 ≤ q)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N) :
    q * (D.card : ℝ) ≤ 2 * N := by
  have hCard := reindexed_card_le_of_same_ball_incidence
    tube gain F b R B S D e hSelectedNonempty hRow
  exact (mul_le_mul_of_nonneg_left hCard hq).trans hGreedy

/-- Concrete dyadic level bound using the actual same-ball incidence,
without any fixed-representative LowerIncidence hypothesis. -/
theorem reindexed_level_of_same_ball_incidence
    [Fintype T]
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hRow : ∀ r ∈ B,
      Kakeya.Seventy7.weight
        (sameBallTubeIncidence tube gain F b R B S D e)
        (fun _ => 1) r ≤ 1)
    (mass : K → ℝ) (level H C deltaPow q N Z : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hdeltaPow : 0 ≤ deltaPow) (hq : 0 ≤ q)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hCapture : level ≤ H * (∑ k ∈ D, mass k))
    (hVolume : ∀ k ∈ D, mass k ≤ C * deltaPow * R)
    (hNormalization : N * deltaPow ≤ Z) :
    q * level ≤ 2 * H * C * Z * R := by
  have hCount := reindexed_budget_of_same_ball_incidence
    tube gain F b R B S D e hSelectedNonempty hRow
    q N hq hGreedy
  exact localized_level_normalized_bound
    D mass level H C deltaPow R q N Z
    hH hC hR hdeltaPow hq hCapture hVolume hCount hNormalization

theorem reindexed_card_le_of_lower_incidence
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hLower : ∃ rep : {j : T // j ∈ B} → {k : K // k ∈ D},
      LowerIncidence
        (reindexedSmallPiece tube gain F b R B S D e) rep) :
    (D.card : ℝ) ≤ (B.card : ℝ) := by
  classical
  let E := reindexedSmallPiece tube gain F b R B S D e
  have hDisjoint : ∀ k k' : {k : K // k ∈ D}, k ≠ k' →
      Disjoint (E k) (E k') := by
    exact reindexedSmallPiece_pairwise_disjoint
      tube gain F b R B S D e hGain hBalls
  have hNonempty : ∀ k : {k : K // k ∈ D}, (E k).Nonempty :=
    reindexedSmallPiece_nonempty tube gain F b R B S D e hSelectedNonempty
  obtain ⟨rep, hRepLower⟩ := hLower
  have hCount := onePiece_full_double_count E rep
    hDisjoint hNonempty hRepLower
  simpa using hCount

theorem reindexed_budget_of_lower_incidence
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hLower : ∃ rep : {j : T // j ∈ B} → {k : K // k ∈ D},
      LowerIncidence
        (reindexedSmallPiece tube gain F b R B S D e) rep)
    (q N : ℝ) (hq : 0 ≤ q)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N) :
    q * (D.card : ℝ) ≤ 2 * N := by
  have hCount := reindexed_card_le_of_lower_incidence
    tube gain F b R B S D e
    hGain hBalls hSelectedNonempty hLower
  calc
    q * (D.card : ℝ) ≤ q * (B.card : ℝ) :=
      mul_le_mul_of_nonneg_left hCount hq
    _ ≤ 2 * N := hGreedy

theorem reindexed_level_of_lower_incidence
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hLower : ∃ rep : {j : T // j ∈ B} → {k : K // k ∈ D},
      LowerIncidence
        (reindexedSmallPiece tube gain F b R B S D e) rep)
    (mass : K → ℝ) (level H C deltaPow q N Z : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hdeltaPow : 0 ≤ deltaPow) (hq : 0 ≤ q)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hCapture : level ≤ H * (∑ k ∈ D, mass k))
    (hVolume : ∀ k ∈ D, mass k ≤ C * deltaPow * R)
    (hNormalization : N * deltaPow ≤ Z) :
    q * level ≤ 2 * H * C * Z * R := by
  have hCount := reindexed_budget_of_lower_incidence
    tube gain F b R B S D e
    hGain hBalls hSelectedNonempty hLower q N hq hGreedy
  exact localized_level_normalized_bound
    D mass level H C deltaPow R q N Z
    hH hC hR hdeltaPow hq hCapture hVolume hCount hNormalization

end ChosenPairs

end Kakeya.Eighty9

namespace Kakeya.Eighty9

section OriginalToSelected

variable {T I X : Type*} [MetricSpace X]

theorem chosen_small_piece_nonempty_of_vitali_subfamily
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (L S : T → Finset I)
    (hSub : ∀ j ∈ B, S j ⊆ L j)
    (hOriginalPiece : ∀ j ∈ B, ∀ i ∈ L j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty) :
    ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty := by
  intro j hj i hi
  exact hOriginalPiece j hj i (hSub j hj hi)

end OriginalToSelected

end Kakeya.Eighty9

namespace Kakeya.Eighty9

section RepresentativeCardinality

variable {T I K X : Type*} [MetricSpace X]

variable [DecidableEq T] [DecidableEq I] [DecidableEq K]

theorem chosenRepresentative_injective
    (B : Finset T) (S : T → Finset I)
    (hNonemptyFiber : ∀ j ∈ B, (S j).Nonempty) :
    Function.Injective (chosenRepresentative B S hNonemptyFiber) := by
  intro j j' heq
  apply Subtype.ext
  have h := congrArg
    (fun p : TubeWiseVitaliLabel B S => p.1.val) heq
  simpa using h

theorem reindexed_card_eq_of_lower_incidence
    (tube gain : T → Set X) (F : Set X)
    (b : T → I → X) (R : ℝ)
    (B : Finset T) (S : T → Finset I) (D : Finset K)
    (e : {k : K // k ∈ D} ≃ TubeWiseVitaliLabel B S)
    (hNonemptyFiber : ∀ j ∈ B, (S j).Nonempty)
    (hGain : ∀ j ∈ B, ∀ j' ∈ B,
      j ≠ j' → Disjoint (gain j) (gain j'))
    (hBalls : ∀ j ∈ B, ∀ i ∈ S j, ∀ i' ∈ S j,
      i ≠ i' → Disjoint (Metric.ball (b j i) R)
        (Metric.ball (b j i') R))
    (hSelectedNonempty : ∀ j ∈ B, ∀ i ∈ S j,
      ((((tube j ∩ gain j) ∩ F) ∩ Metric.ball (b j i) R)).Nonempty)
    (hLower : ∃ rep : {j : T // j ∈ B} → {k : K // k ∈ D},
      LowerIncidence
        (reindexedSmallPiece tube gain F b R B S D e) rep) :
    D.card = B.card := by
  classical
  have hUpper := reindexed_card_le_of_lower_incidence
    tube gain F b R B S D e
    hGain hBalls hSelectedNonempty hLower
  have hChosenCard : B.card ≤ Fintype.card (TubeWiseVitaliLabel B S) := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective
        (chosenRepresentative B S hNonemptyFiber)
        (chosenRepresentative_injective B S hNonemptyFiber))
  have hReindexedCard : Fintype.card (TubeWiseVitaliLabel B S) = D.card := by
    calc
      Fintype.card (TubeWiseVitaliLabel B S) =
          Fintype.card {k : K // k ∈ D} := Fintype.card_congr e.symm
      _ = D.card := by simp
  have hLowerCard : B.card ≤ D.card := hChosenCard.trans hReindexedCard.le
  have hUpperNat : D.card ≤ B.card := by exact_mod_cast hUpper
  exact Nat.le_antisymm hUpperNat hLowerCard

end RepresentativeCardinality

end Kakeya.Eighty9
