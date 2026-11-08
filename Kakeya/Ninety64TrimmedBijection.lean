module
public import Kakeya.Ninety21Bijection

/-!
# KakeyaNinety64: Theorem 4.2 for actual trimmed pieces; Theorem 4.6 for counts

The matching in this module is INTERSECTION-compatible and uses only
ORIGINAL tubes. It is Theorem 4.2's finite Hall argument, reusing the
repository's `intersecting_matching_of_degree_bounds`.

Theorem 4.6 has a different job: its exceptional-ball estimates control
cardinalities. In particular, we do NOT use its auxiliary/nonintersecting
tube assignment to build the intersection-compatible matching.

Theorem 4.2 applied to ALL actual pieces gives a bijection from those pieces
onto distinct tube labels. If a later theorem additionally requires the
bijection to fix every selected index B, then Hall must instead be applied
to the candidates OUTSIDE B. That is a stronger, separate condition.
-/

@[expose] public section

namespace Kakeya.Ninety64

open Classical in
/-- Theorem 4.2, matching stage. The left and right degrees use the SAME
    intersection relation, and every representative is an original tube. -/
theorem theorem42_matching
    {P T X : Type*} [Fintype P] [Fintype T]
    (piece : P → Set X) (tube : T → Set X) (q bound : ℝ)
    (hq : 0 < q) (hDegreeScale : bound ≤ q)
    (hLeft : ∀ p : P,
      q ≤ ((Finset.univ.filter
        (fun r : T => (piece p ∩ tube r).Nonempty)).card : ℝ))
    (hRight : ∀ r : T,
      ((Finset.univ.filter
        (fun p : P => (piece p ∩ tube r).Nonempty)).card : ℝ) ≤ bound) :
    ∃ σ : P → T, Function.Injective σ ∧
      ∀ p, (piece p ∩ tube (σ p)).Nonempty := by
  classical
  let hit : P → T → Prop :=
    fun p r => (piece p ∩ tube r).Nonempty
  exact Kakeya.Ninety21.intersecting_matching_of_degree_bounds
    hit q bound hq hDegreeScale hLeft hRight

open Classical in
/-- Theorem 4.2 gives an intersection-compatible bijection from the ACTUAL
    pieces onto their distinct original-tube representatives. The codomain
    `D` is the image of the Hall matching; no auxiliary tubes are adjoined. -/
theorem theorem42_actual_piece_bijection
    {P T X : Type*} [Fintype P] [Fintype T]
    (piece : P → Set X) (tube : T → Set X) (q bound : ℝ)
    (hq : 0 < q) (hDegreeScale : bound ≤ q)
    (hLeft : ∀ p : P,
      q ≤ ((Finset.univ.filter
        (fun r : T => (piece p ∩ tube r).Nonempty)).card : ℝ))
    (hRight : ∀ r : T,
      ((Finset.univ.filter
        (fun p : P => (piece p ∩ tube r).Nonempty)).card : ℝ) ≤ bound) :
    ∃ (D : Finset T) (e : P ≃ {r : T // r ∈ D}),
      (∀ p, (piece p ∩ tube (e p).val).Nonempty) ∧
      D.card = Fintype.card P := by
  classical
  obtain ⟨σ, hσ, hhit⟩ :=
    theorem42_matching piece tube q bound hq hDegreeScale hLeft hRight
  let D : Finset T := Finset.univ.image σ
  let f : P → {r : T // r ∈ D} := fun p =>
    ⟨σ p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro p p' h
    apply hσ
    exact congrArg Subtype.val h
  have hf_surj : Function.Surjective f := by
    intro r
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp r.property
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp
  let e : P ≃ {r : T // r ∈ D} :=
    Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨D, e, ?_, ?_⟩
  · intro p
    change (piece p ∩ tube (σ p)).Nonempty
    exact hhit p
  · have hcard := Fintype.card_congr e
    simpa only [Fintype.card_coe] using hcard.symm

/-!
The unrestricted `B ⊕ P` form requires no separate theorem: instantiate
`theorem42_actual_piece_bijection` with the piece type
`({r : T // r ∈ B} ⊕ P)`. The fixed-selected-label version below is the
additional statement needed when `e (Sum.inl r)` must be `r`.
-/

/-! ## Restricted Hall construction for the optional fixed-selected corollary -/

-- The restricted incidence relation is proved first. Keeping the matching
-- separate from the equivalence construction makes Lean elaboration smaller.
set_option maxHeartbeats 1000000 in
-- This finite Hall specialization needs additional elaboration heartbeats.
open Classical in
/-- Hall's theorem applied to the ORIGINAL tubes outside the reserved set `B`.
    This is a genuinely intersecting matching of the actual trimmed pieces. -/
theorem theorem42_restricted_matching
    {P T X : Type*} [Fintype P] [Fintype T]
    (piece : P → Set X) (tube : T → Set X)
    (B : Finset T) (q bound : ℝ)
    (hq : 0 < q) (hbound : 0 ≤ bound) (hDegreeScale : bound ≤ q)
    (hLeftOutside : ∀ p : P,
      q ≤ ((Finset.univ.filter
        (fun r : T => r ∉ B ∧ (piece p ∩ tube r).Nonempty)).card : ℝ))
    (hRight : ∀ r : T, r ∉ B →
      ((Finset.univ.filter
        (fun p : P => (piece p ∩ tube r).Nonempty)).card : ℝ) ≤ bound) :
    ∃ σ : P → T, Function.Injective σ ∧
      ∀ p, σ p ∉ B ∧ (piece p ∩ tube (σ p)).Nonempty := by
  classical
  let hit : P → T → Prop :=
    fun p r => r ∉ B ∧ (piece p ∩ tube r).Nonempty
  -- The pre-existing Hall theorem elaborates its filter with the classical
  -- decidability instance for the *opaque* local relation `hit`.
  -- Give that instance explicitly, so Lean does not instead synthesize
  -- `instDecidableAnd` after unfolding the body of `hit`.
  have hL : ∀ p : P,
      q ≤ ((@Finset.filter T (hit p)
        (fun r => Classical.propDecidable (hit p r)) Finset.univ).card : ℝ) := by
    intro p
    have heq :
        (@Finset.filter T (hit p)
          (fun r => Classical.propDecidable (hit p r)) Finset.univ) =
        Finset.univ.filter
          (fun r : T => r ∉ B ∧ (piece p ∩ tube r).Nonempty) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit]
    rw [heq]
    exact hLeftOutside p
  have hR : ∀ r : T,
      ((@Finset.filter P (fun p : P => hit p r)
        (fun p => Classical.propDecidable (hit p r)) Finset.univ).card : ℝ) ≤ bound := by
    intro r
    by_cases hr : r ∈ B
    · have hempty :
          (@Finset.filter P (fun p : P => hit p r)
            (fun p => Classical.propDecidable (hit p r)) Finset.univ) = ∅ := by
        ext p
        simp [hit, hr]
      rw [hempty]
      simpa using hbound
    · have heq :
          (@Finset.filter P (fun p : P => hit p r)
            (fun p => Classical.propDecidable (hit p r)) Finset.univ) =
          Finset.univ.filter
            (fun p : P => (piece p ∩ tube r).Nonempty) := by
        ext p
        simp [hit, hr]
      rw [heq]
      exact hRight r hr
  obtain ⟨σ, hσ, hhit⟩ :=
    Kakeya.Ninety21.intersecting_matching_of_degree_bounds
      hit q bound hq hDegreeScale hL hR
  refine ⟨σ, hσ, ?_⟩
  intro p
  exact hhit p

set_option maxHeartbeats 1000000 in
-- Extending the dependent matching equivalence requires a local heartbeat limit.
open Classical in
/-- Optional fixed-selected-index form of Theorem 4.2.
    The matching has already been proved separately, so here we only extend
    its injective map by the identity on the reserved selected indices. -/
theorem theorem42_bijection_fixing_selected
    {P T X : Type*} [Fintype P] [Fintype T]
    (piece : P → Set X) (tube : T → Set X)
    (B : Finset T) (q bound : ℝ)
    (hq : 0 < q) (hbound : 0 ≤ bound) (hDegreeScale : bound ≤ q)
    (hLeftOutside : ∀ p : P,
      q ≤ ((Finset.univ.filter
        (fun r : T => r ∉ B ∧ (piece p ∩ tube r).Nonempty)).card : ℝ))
    (hRight : ∀ r : T, r ∉ B →
      ((Finset.univ.filter
        (fun p : P => (piece p ∩ tube r).Nonempty)).card : ℝ) ≤ bound) :
    ∃ (D : Finset T)
      (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D}),
      B ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p, (e (Sum.inr p)).val ∉ B ∧
        (piece p ∩ tube (e (Sum.inr p)).val).Nonempty) ∧
      D.card = B.card + Fintype.card P := by
  classical
  obtain ⟨σ, hσ, hgood⟩ :=
    theorem42_restricted_matching piece tube B q bound
      hq hbound hDegreeScale hLeftOutside hRight
  obtain ⟨D, e, hBD, hfix, hAssign, hCard⟩ :=
    Kakeya.Ninety21.extend_matching_to_bijection B σ hσ
      (fun p => (hgood p).1)
  refine ⟨D, e, hBD, hfix, ?_, hCard⟩
  intro p
  simpa only [hAssign p] using hgood p

/-! ## Theorem 4.6: cardinality estimates ONLY -/

open Classical in
/-- The combinatorial counting input to Theorem 4.6: each exceptional
    piece has a unique `(selected tube, Vitali ball)` label. -/
theorem exceptional_piece_count_of_pair_injective
    {E T J : Type*} [Fintype E]
    (B : Finset T) (Jexc : Finset J)
    (outer : E → T) (ball : E → J)
    (hOuter : ∀ e, outer e ∈ B)
    (hBall : ∀ e, ball e ∈ Jexc)
    (hUnique : Function.Injective (fun e => (outer e, ball e))) :
    Fintype.card E ≤ B.card * Jexc.card := by
  classical
  let f : E → ({r : T // r ∈ B} × {j : J // j ∈ Jexc}) :=
    fun e => (⟨outer e, hOuter e⟩, ⟨ball e, hBall e⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply hUnique
    apply Prod.ext
    · exact congrArg (fun x : ({r : T // r ∈ B} × {j : J // j ∈ Jexc}) =>
        x.1.val) hab
    · exact congrArg (fun x : ({r : T // r ∈ B} × {j : J // j ∈ Jexc}) =>
        x.2.val) hab
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe] using hc

open Classical in
/-- Theorem 4.6's exception count from Lemma 4.4's packing estimate.
    Importantly: no representative map or auxiliary tube appears here. -/
theorem exceptional_piece_count_of_packing
    {E T J : Type*} [Fintype E]
    (B : Finset T) (Jexc : Finset J) (C : ℕ)
    (outer : E → T) (ball : E → J)
    (hOuter : ∀ e, outer e ∈ B)
    (hBall : ∀ e, ball e ∈ Jexc)
    (hUnique : Function.Injective (fun e => (outer e, ball e)))
    (hPacked : Jexc.card ≤ C) :
    Fintype.card E ≤ C * B.card := by
  calc
    Fintype.card E ≤ B.card * Jexc.card :=
      exceptional_piece_count_of_pair_injective
        B Jexc outer ball hOuter hBall hUnique
    _ ≤ B.card * C := Nat.mul_le_mul_left B.card hPacked
    _ = C * B.card := Nat.mul_comm _ _

open Classical in
/-- Combine the exceptional-piece bound with greedy's `q |B| ≤ 2N`.
    This is only a COUNTING statement. -/
theorem exceptional_piece_scaled_budget
    {E T J : Type*} [Fintype E] [Fintype T]
    (B : Finset T) (Jexc : Finset J) (C q : ℕ)
    (outer : E → T) (ball : E → J)
    (hOuter : ∀ e, outer e ∈ B)
    (hBall : ∀ e, ball e ∈ Jexc)
    (hUnique : Function.Injective (fun e => (outer e, ball e)))
    (hPacked : Jexc.card ≤ C)
    (hGreedy : q * B.card ≤ 2 * Fintype.card T) :
    q * Fintype.card E ≤ 2 * C * Fintype.card T := by
  have hCount : Fintype.card E ≤ C * B.card :=
    exceptional_piece_count_of_packing
      B Jexc C outer ball hOuter hBall hUnique hPacked
  calc
    q * Fintype.card E ≤ q * (C * B.card) :=
      Nat.mul_le_mul_left q hCount
    _ = (q * B.card) * C := by ring
    _ ≤ (2 * Fintype.card T) * C :=
      Nat.mul_le_mul_right C hGreedy
    _ = 2 * C * Fintype.card T := by ring

end Kakeya.Ninety64
