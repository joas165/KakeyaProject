module
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Data.Sum.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic

/-!
# Ninety21: Hall matching and a bijection fixing the selected tubes

`P` is the finite type of remaining piece labels, `T` the finite type of
original tube indices, and `B` the selected indices. Theorem 4.4 is proved
from its explicit no-dominant-hairbrush hypothesis. No geometric containment
is inferred from matching; the conclusion preserves exactly nonintersection.
-/

@[expose] public section

open scoped BigOperators

namespace Kakeya.Ninety21

variable {P T X : Type*} [Fintype P]

open Classical in
/-- Hall's condition follows if each admissible set alone has enough elements
to represent all pieces. Empty piece types are included. -/
theorem matching_of_uniform_card_bound (A : P → Finset T)
    (hA : ∀ p, Fintype.card P ≤ (A p).card) :
    ∃ σ : P → T, Function.Injective σ ∧ ∀ p, σ p ∈ A p := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp
  intro S
  by_cases hs : S.Nonempty
  · obtain ⟨p, hp⟩ := hs
    exact (S.card_le_univ.trans (hA p)).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem A hp))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

open Classical in
/-- General form of Theorem 4.4: each piece leaves enough indices after
excluding both selected tubes and intersecting tubes. -/
theorem nonintersecting_matching_of_room [Fintype T]
    (hit : P → T → Prop) (B : Finset T)
    (hRoom : ∀ p, Fintype.card P + B.card +
      (Finset.univ.filter (hit p)).card ≤ Fintype.card T) :
    ∃ σ : P → T, Function.Injective σ ∧
      ∀ p, σ p ∉ B ∧ ¬ hit p (σ p) := by
  classical
  let bad : P → Finset T := fun p => B ∪ Finset.univ.filter (hit p)
  let A : P → Finset T := fun p => Finset.univ \ bad p
  have hA : ∀ p, Fintype.card P ≤ (A p).card := by
    intro p
    have hb : (bad p).card ≤ B.card + (Finset.univ.filter (hit p)).card :=
      Finset.card_union_le _ _
    have hc : (A p).card = Fintype.card T - (bad p).card := by
      simp only [A, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hr := hRoom p
    omega
  obtain ⟨σ, hσ, hmem⟩ := matching_of_uniform_card_bound A hA
  refine ⟨σ, hσ, ?_⟩
  intro p
  have hp := hmem p
  simpa [A, bad, not_or] using hp

open Classical in
/-- The paper's cardinal assumptions, with denominators cleared:
`|P| ≤ N/4`, `|B| ≤ N/4`, and `d(p) ≤ N/2`. -/
theorem nonintersecting_matching_of_quarter_half_bounds [Fintype T]
    (hit : P → T → Prop) (B : Finset T)
    (hP : 4 * Fintype.card P ≤ Fintype.card T)
    (hB : 4 * B.card ≤ Fintype.card T)
    (hDegree : ∀ p, 2 * (Finset.univ.filter (hit p)).card ≤ Fintype.card T) :
    ∃ σ : P → T, Function.Injective σ ∧
      ∀ p, σ p ∉ B ∧ ¬ hit p (σ p) := by
  apply nonintersecting_matching_of_room hit B
  intro p
  have hd := hDegree p
  omega

open Classical in
/-- Theorem 4.4's matching, using `q ≥ 8` and the greedy budget directly. -/
theorem nonintersecting_matching_of_greedy [Fintype T]
    (hit : P → T → Prop) (B : Finset T) (q : ℕ)
    (hq : 8 ≤ q)
    (hGreedy : q * B.card ≤ 2 * Fintype.card T)
    (hP : 4 * Fintype.card P ≤ Fintype.card T)
    (hDegree : ∀ p, 2 * (Finset.univ.filter (hit p)).card ≤ Fintype.card T) :
    ∃ σ : P → T, Function.Injective σ ∧
      ∀ p, σ p ∉ B ∧ ¬ hit p (σ p) := by
  apply nonintersecting_matching_of_quarter_half_bounds hit B hP
  · nlinarith
  · exact hDegree

open Classical in
/-- An injective assignment outside `B` extends to an actual equivalence
`B ⊔ P ≃ D`, fixing the selected indices and retaining every piece label. -/
theorem extend_matching_to_bijection
    (B : Finset T) (σ : P → T) (hσ : Function.Injective σ)
    (hout : ∀ p, σ p ∉ B) :
    ∃ (D : Finset T) (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D}),
      B ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p, (e (Sum.inr p)).val = σ p) ∧
      D.card = B.card + Fintype.card P := by
  classical
  let D : Finset T := B ∪ Finset.univ.image σ
  let f : ({r : T // r ∈ B} ⊕ P) → {r : T // r ∈ D} :=
    Sum.elim
      (fun r => ⟨r.val, Finset.mem_union_left _ r.property⟩)
      (fun p => ⟨σ p, Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p, Finset.mem_univ p, rfl⟩)⟩)
  have hsum : Function.Injective (Sum.elim (fun r : {r : T // r ∈ B} => r.val) σ) := by
    apply Subtype.val_injective.sumElim hσ
    intro r p heq
    exact hout p (heq ▸ r.property)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply hsum
      have hv : (f a).val = (f b).val := congrArg (fun z : {r : T // r ∈ D} => z.val) hab
      cases a <;> cases b <;> simpa only [f, Sum.elim_inl, Sum.elim_inr] using hv
    · intro r
      rcases Finset.mem_union.mp r.property with hr | hr
      · exact ⟨Sum.inl ⟨r.val, hr⟩, Subtype.ext rfl⟩
      · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hr
        exact ⟨Sum.inr p, Subtype.ext hp⟩
  let e := Equiv.ofBijective f hf
  refine ⟨D, e, Finset.subset_union_left, ?_, ?_, ?_⟩
  · intro r
    rfl
  · intro p
    rfl
  · have hc := Fintype.card_congr e
    simpa using hc.symm

open Classical in
/-- Theorem 4.4, including the bijection and its nonintersection property. -/
theorem nonintersecting_bijection_of_greedy [Fintype T]
    (hit : P → T → Prop) (B : Finset T) (q : ℕ)
    (hq : 8 ≤ q)
    (hGreedy : q * B.card ≤ 2 * Fintype.card T)
    (hP : 4 * Fintype.card P ≤ Fintype.card T)
    (hDegree : ∀ p, 2 * (Finset.univ.filter (hit p)).card ≤ Fintype.card T) :
    ∃ (D : Finset T) (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D}),
      B ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p, (e (Sum.inr p)).val ∉ B ∧ ¬ hit p (e (Sum.inr p)).val) ∧
      D.card = B.card + Fintype.card P := by
  obtain ⟨σ, hσ, hgood⟩ :=
    nonintersecting_matching_of_greedy hit B q hq hGreedy hP hDegree
  obtain ⟨D, e, hBD, hfix, hassign, hcard⟩ :=
    extend_matching_to_bijection B σ hσ (fun p => (hgood p).1)
  refine ⟨D, e, hBD, hfix, ?_, hcard⟩
  intro p
  simpa only [hassign p] using hgood p

open Classical in
/-- Geometric specialization: remaining pieces receive distinct original tube
indices outside B, with empty intersection, and selected indices are fixed. -/
theorem localized_nonintersecting_bijection [Fintype T]
    (piece : P → Set X) (tube : T → Set X) (B : Finset T) (q : ℕ)
    (hq : 8 ≤ q)
    (hGreedy : q * B.card ≤ 2 * Fintype.card T)
    (hP : 4 * Fintype.card P ≤ Fintype.card T)
    (hDegree : ∀ p,
      2 * (Finset.univ.filter (fun r => (piece p ∩ tube r).Nonempty)).card ≤
        Fintype.card T) :
    ∃ (D : Finset T) (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D}),
      B ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p, (e (Sum.inr p)).val ∉ B ∧ piece p ∩ tube (e (Sum.inr p)).val = ∅) ∧
      D.card = B.card + Fintype.card P := by
  obtain ⟨D, e, hBD, hfix, hgood, hcard⟩ := nonintersecting_bijection_of_greedy
    (fun p r => (piece p ∩ tube r).Nonempty) B q hq hGreedy hP hDegree
  refine ⟨D, e, hBD, hfix, ?_, hcard⟩
  intro p
  exact ⟨(hgood p).1, Set.not_nonempty_iff_eq_empty.mp (hgood p).2⟩

open Classical in
/-- The double-counting form of Theorem 4.2. The right degree bound may be a
real number (e.g. `C * q^(1/(n-1))`); the relevant-scale input is `bound ≤ q`.
No global bound on the total number of pieces is needed for this Hall proof. -/
theorem intersecting_matching_of_degree_bounds [Fintype T]
    (hit : P → T → Prop) (q bound : ℝ) (hq : 0 < q) (hbq : bound ≤ q)
    (hLeft : ∀ p, q ≤ ((Finset.univ.filter (hit p)).card : ℝ))
    (hRight : ∀ r, ((Finset.univ.filter (fun p => hit p r)).card : ℝ) ≤ bound) :
    ∃ σ : P → T, Function.Injective σ ∧ ∀ p, hit p (σ p) := by
  classical
  let A : P → Finset T := fun p => Finset.univ.filter (hit p)
  have hHall : ∀ S : Finset P, S.card ≤ (S.biUnion A).card := by
    intro S
    let U := S.biUnion A
    have hlow : ∀ p ∈ S, q ≤ ((U.bipartiteAbove hit p).card : ℝ) := by
      intro p hp
      have heq : U.bipartiteAbove hit p = A p := by
        ext r
        simp only [Finset.mem_bipartiteAbove, A, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · exact fun h => h.2
        · intro hr
          exact ⟨Finset.mem_biUnion.mpr ⟨p, hp, by simpa [A] using hr⟩, hr⟩
      rw [heq]
      exact hLeft p
    have hupp : ∀ r ∈ U, ((S.bipartiteBelow hit r).card : ℝ) ≤ bound := by
      intro r _
      have hc : (S.bipartiteBelow hit r).card ≤
          (Finset.univ.filter (fun p => hit p r)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ p, ((Finset.mem_bipartiteBelow hit).mp hp).2⟩
      have hc' : ((S.bipartiteBelow hit r).card : ℝ) ≤
          ((Finset.univ.filter (fun p => hit p r)).card : ℝ) := by exact_mod_cast hc
      exact hc'.trans (hRight r)
    have hedge := Finset.card_nsmul_le_card_nsmul (R := ℝ) hit hlow hupp
    have hedge' : (S.card : ℝ) * q ≤ (U.card : ℝ) * bound := by
      simpa only [nsmul_eq_mul] using hedge
    have hbound := mul_le_mul_of_nonneg_left hbq (Nat.cast_nonneg U.card : (0 : ℝ) ≤ U.card)
    have hcard : (S.card : ℝ) ≤ (U.card : ℝ) := by nlinarith
    exact_mod_cast hcard
  obtain ⟨σ, hσ, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp hHall
  exact ⟨σ, hσ, fun p => (Finset.mem_filter.mp (hmem p)).2⟩

end Kakeya.Ninety21
