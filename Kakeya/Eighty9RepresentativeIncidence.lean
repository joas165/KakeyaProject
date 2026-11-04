module
public import Mathlib
public import Kakeya.Eighty9VitaliDoubleCount
public import Kakeya.SelectionComparison
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic

/-!
# Representative incidence

Canonical lower-incidence predicates and their consequences for disjoint pieces.
-/

@[expose] public section

namespace Kakeya.Eighty9

section OneTestingPiecePerTube

variable {J P X : Type*}

open Set

/-- The incidence relation between a selected representative and a piece. -/
def representativeIncidence
    {P X J : Type*}
    (E : P → Set X) (rep : J → P)
    (j : J) (p : P) : Prop :=
  (E p ∩ E (rep j)).Nonempty

/-- Canonical lower-incidence predicate used throughout the project. -/
def LowerIncidence (E : P → Set X) (rep : J → P) : Prop :=
  ∀ p : P, ∃ j : J, representativeIncidence E rep j p

/-- The composition E ∘ rep, with codomain restricted
to the range of E. -/
def composedIntoRange
    {P X J : Type*}
    (E : P → Set X) (rep : J → P) :
    J → {s : Set X // s ∈ Set.range E} :=
  fun j => ⟨E (rep j), ⟨rep j, rfl⟩⟩

theorem rep_surjective_of_composed
    {P X J : Type*}
    (E : P → Set X) (rep : J → P)
    (h_inj : Function.Injective E)
    (h_surj : Function.Surjective
      (composedIntoRange E rep)) :
    Function.Surjective rep := by
  intro p
  obtain ⟨j, hj⟩ :=
    h_surj ⟨E p, ⟨p, rfl⟩⟩
  refine ⟨j, h_inj ?_⟩
  exact congrArg Subtype.val hj

/-- If k is bijective, then E ∘ k covers the range of E.
The codomain is `Set.range E`, not the entire powerset `Set X`. -/
theorem composedIntoRange_surjective_of_bijective
    {P X J : Type*}
    (E : P → Set X) (k : J → P)
    (hk : Function.Bijective k) :
    Function.Surjective (composedIntoRange E k) := by
  intro s
  obtain ⟨p, hp⟩ := s.property
  obtain ⟨j, hj⟩ := hk.2 p
  refine ⟨j, Subtype.ext ?_⟩
  change E (k j) = s.val
  rw [hj, hp]

theorem onePieceIncidence_composed
    {P X J : Type*}
    (E : P → Set X) (rep : J → P)
    (h_prop : ∀ p : P, (E p).Nonempty)
    (h_surj : Function.Surjective
      (composedIntoRange E rep)) :
    LowerIncidence E rep := by
  intro p
  obtain ⟨j, hj⟩ :=
    h_surj ⟨E p, ⟨p, rfl⟩⟩
  have hE : E (rep j) = E p :=
    congrArg Subtype.val hj
  obtain ⟨x, hx⟩ := h_prop p
  refine ⟨j, x, hx, ?_⟩
  change x ∈ E (rep j)
  rw [hE]
  exact hx

theorem onePieceIncidence
    {P X J : Type*}
    (E : P → Set X) (rep : J → P)
    (h_prop : ∀ p : P, (E p).Nonempty)
    (h_rep_surj : Function.Surjective rep) :
    LowerIncidence E rep := by
  intro p
  obtain ⟨j, hj⟩ := h_rep_surj p
  refine ⟨j, ?_⟩
  change (E p ∩ E (rep j)).Nonempty
  rw [hj]
  obtain ⟨x, hx⟩ := h_prop p
  exact ⟨x, hx, hx⟩

/-- Nonempty, pairwise-disjoint pieces have distinct geometric sets. -/
theorem pieceMap_injective_of_disjoint_nonempty
    {P X : Type*} (E : P → Set X)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty) :
    Function.Injective E := by
  intro p p' hEq
  by_contra hne
  obtain ⟨x, hx⟩ := hNonempty p
  have hx' : x ∈ E p' := by
    rw [← hEq]
    exact hx
  exact (Set.disjoint_left.mp (hDisjoint p p' hne)) hx hx'

/-- The injectivity route: range-surjectivity of the composed piece map
implies surjectivity of `rep`, which gives the canonical lower incidence. -/
theorem lowerIncidence_of_composed_injective
    {P X J : Type*} (E : P → Set X) (rep : J → P)
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hInjective : Function.Injective E)
    (hRange : Function.Surjective (composedIntoRange E rep)) :
    LowerIncidence E rep := by
  have hRepSurj : Function.Surjective rep :=
    rep_surjective_of_composed E rep hInjective hRange
  exact onePieceIncidence E rep hNonempty hRepSurj

theorem lowerIncidence_of_bijective
    {P X J : Type*}
    (E : P → Set X) (k : J → P)
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hk : Function.Bijective k) :
    LowerIncidence E k := by
  exact onePieceIncidence E k hNonempty hk.2

theorem onePieceIncidence_iff_eq
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (j : J) (p : P) :
    representativeIncidence E rep j p ↔ p = rep j := by
  constructor
  · intro hInc
    by_contra hne
    obtain ⟨x, hx, hy⟩ := hInc
    exact (Set.disjoint_left.mp (hDisjoint p (rep j) hne)) hx hy
  · intro hp
    subst p
    obtain ⟨x, hx⟩ := hNonempty (rep j)
    exact ⟨x, hx, hx⟩

end OneTestingPiecePerTube

section FiniteCount

variable {J P X : Type*} [Fintype P] [Fintype J]

theorem onePiece_row_weight_eq_one
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (j : J) :
    Kakeya.Seventy7.weight (representativeIncidence E rep) (fun _ => 1) j = 1 := by
  classical
  unfold Kakeya.Seventy7.weight
  have hIff : ∀ p : P, representativeIncidence E rep j p ↔ p = rep j :=
    fun p => onePieceIncidence_iff_eq E rep hDisjoint hNonempty j p
  simp_rw [hIff]
  simp

theorem onePiece_selected_double_count
    (E : P → Set X) (rep : J → P) (B : Finset J)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hCoveredOnB : ∀ p : P, ∃ j ∈ B, representativeIncidence E rep j p) :
    (Fintype.card P : ℝ) ≤ (B.card : ℝ) := by
  apply selected_incidence_double_count (representativeIncidence E rep) B hCoveredOnB
  intro j hj
  exact (onePiece_row_weight_eq_one E rep hDisjoint hNonempty j).le

/-- Full selected-tube double count from the canonical lower-incidence predicate. -/
theorem onePiece_full_double_count
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hLower : LowerIncidence E rep) :
    (Fintype.card P : ℝ) ≤ (Fintype.card J : ℝ) := by
  classical
  have hCoverage : ∀ p : P,
      ∃ j ∈ (Finset.univ : Finset J), representativeIncidence E rep j p := by
    intro p
    obtain ⟨j, hj⟩ := hLower p
    exact ⟨j, Finset.mem_univ _, hj⟩
  have h := onePiece_selected_double_count E rep
    (Finset.univ : Finset J) hDisjoint hNonempty hCoverage
  simpa using h

/-- Use the uploaded range-surjectivity lemma directly in the finite count. -/
theorem onePiece_full_double_count_of_composed_range
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hRange : Function.Surjective (composedIntoRange E rep)) :
    (Fintype.card P : ℝ) ≤ (Fintype.card J : ℝ) := by
  exact onePiece_full_double_count E rep hDisjoint hNonempty
    (onePieceIncidence_composed E rep hNonempty hRange)

/-- A bijective representative map proves lower incidence and the count. -/
theorem onePiece_full_double_count_of_bijective
    (E : P → Set X) (rep : J → P)
    (hDisjoint : ∀ p p' : P, p ≠ p' → Disjoint (E p) (E p'))
    (hNonempty : ∀ p : P, (E p).Nonempty)
    (hBij : Function.Bijective rep) :
    (Fintype.card P : ℝ) ≤ (Fintype.card J : ℝ) := by
  exact onePiece_full_double_count E rep hDisjoint hNonempty
    (lowerIncidence_of_bijective E rep hNonempty hBij)

end FiniteCount

end Kakeya.Eighty9
