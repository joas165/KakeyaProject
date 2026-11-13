module
public import Kakeya.Ninety21PaperDoubleCount
public import Kakeya.Ninety64TrimmedBijection

/-!
# Theorem 4.6 Hall equivalence

The matching fixes selected tube labels, assigns distinct nonintersecting
original tubes to regular retained pieces, and assigns formal auxiliary
labels to exceptional retained pieces. The regular-piece budget and
dyadic lower threshold are supplied by the geometric counting interface.
-/

@[expose] public section
open MeasureTheory
namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Regular pieces with tube-intersection degree at most N/2. -/
abbrev PaperRegularLabel
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :=
  {p : {k : K // k ∈ s.P m} // p ∈ paperRegularPieces μ tubes n s m}

/-- Exceptional pieces with tube-intersection degree greater than N/2. -/
abbrev PaperExceptionalLabel
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :=
  {p : {k : K // k ∈ s.P m} // p ∈ paperExceptionalPieces μ tubes n s m}

/-- Original tube indices and exceptional-piece labels. -/
abbrev PaperExtendedLabel
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :=
  T ⊕ PaperExceptionalLabel μ tubes n s m

/-- Selected indices embedded into the extended label set. -/
noncomputable def paperSelectedExtended
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Finset (PaperExtendedLabel μ tubes n s m) := by
  classical
  exact (s.B m).image Sum.inl

/-- Scale and regular-piece cardinality bounds for the Theorem 4.6 construction. -/
structure Paper46ConstructionData
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) where
  q : ℕ
  hq : 8 ≤ q
  hScale : (q : ℝ) = Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  hRegularBudget : 4 * (paperRegularPieces μ tubes n s m).card ≤ Fintype.card T

/-- Extend the regular nonintersecting matching and exceptional labels to an equivalence fixing
    selected indices. -/
theorem exists_paper46_hall_equiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    ∃ (D : Finset (PaperExtendedLabel μ tubes n s m))
      (e : ({r : PaperExtendedLabel μ tubes n s m //
          r ∈ paperSelectedExtended μ tubes n s m} ⊕
          (PaperRegularLabel μ tubes n s m ⊕
            PaperExceptionalLabel μ tubes n s m)) ≃
          {r : PaperExtendedLabel μ tubes n s m // r ∈ D}),
      paperSelectedExtended μ tubes n s m ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p : PaperRegularLabel μ tubes n s m,
        ∃ r : T,
          (e (Sum.inr (Sum.inl p))).val = Sum.inl r ∧
          r ∉ s.B m ∧
          ¬(s.retainedPiece m (Sum.inr p.val) ∩ tubes r).Nonempty) ∧
      (∀ p : PaperExceptionalLabel μ tubes n s m,
        (e (Sum.inr (Sum.inr p))).val = Sum.inr p) ∧
      D.card = (paperSelectedExtended μ tubes n s m).card +
        Fintype.card (PaperRegularLabel μ tubes n s m ⊕
          PaperExceptionalLabel μ tubes n s m) := by
  classical
  let Reg := PaperRegularLabel μ tubes n s m
  let Exc := PaperExceptionalLabel μ tubes n s m
  let hit : Reg → T → Prop := fun p r =>
    (s.retainedPiece m (Sum.inr p.val) ∩ tubes r).Nonempty
  have hGreedy : a.q * (s.B m).card ≤ 2 * Fintype.card T := by
    have h := s.hGreedy m
    rw [← a.hScale] at h
    exact_mod_cast h
  have hDegree : ∀ p : Reg,
      2 * (Finset.univ.filter (fun r : T => hit p r)).card ≤
        Fintype.card T := by
    intro p
    have hp := (mem_paperRegularPieces μ tubes n s m p.val).mp p.property
    change 2 * (Finset.univ.filter (fun r : T => hit p r)).card ≤
      Fintype.card T at hp
    exact hp
  have hOrdinary : 4 * Fintype.card Reg ≤ Fintype.card T := by
    change 4 * Fintype.card (↥(paperRegularPieces μ tubes n s m)) ≤
      Fintype.card T
    simpa only [Fintype.card_coe] using a.hRegularBudget
  obtain ⟨σ₀, hσ₀, hgood⟩ :=
    Kakeya.Ninety21.nonintersecting_matching_of_greedy
      hit (s.B m) a.q a.hq hGreedy hOrdinary hDegree
  let σ : Reg ⊕ Exc → (T ⊕ Exc) :=
    Sum.elim (fun p => Sum.inl (σ₀ p)) Sum.inr
  have hσ : Function.Injective σ := by
    intro u v huv
    cases u with
    | inl p =>
      cases v with
      | inl p' =>
        change (Sum.inl (σ₀ p) : T ⊕ Exc) = Sum.inl (σ₀ p') at huv
        have hp : σ₀ p = σ₀ p' := Sum.inl.inj huv
        exact congrArg (fun x : Reg => (Sum.inl x : Reg ⊕ Exc)) (hσ₀ hp)
      | inr p' =>
        have h : (Sum.inl (σ₀ p) : T ⊕ Exc) = Sum.inr p' := by
          exact huv
        cases h
    | inr p =>
      cases v with
      | inl p' =>
        have h : (Sum.inr p : T ⊕ Exc) = Sum.inl (σ₀ p') := by
          exact huv
        cases h
      | inr p' =>
        change (Sum.inr p : T ⊕ Exc) = Sum.inr p' at huv
        have hp : p = p' := Sum.inr.inj huv
        exact congrArg (fun x : Exc => (Sum.inr x : Reg ⊕ Exc)) hp
  have hOutside : ∀ p : Reg ⊕ Exc,
      σ p ∉ paperSelectedExtended μ tubes n s m := by
    intro p
    cases p with
    | inl p =>
      change (Sum.inl (σ₀ p) : T ⊕ Exc) ∉
        paperSelectedExtended μ tubes n s m
      intro hmem
      obtain ⟨r, hrB, hrEq⟩ := Finset.mem_image.mp hmem
      have hr : r = σ₀ p := Sum.inl.inj hrEq
      exact (hgood p).1 (hr ▸ hrB)
    | inr p =>
      change (Sum.inr p : T ⊕ Exc) ∉
        paperSelectedExtended μ tubes n s m
      intro hmem
      obtain ⟨r, _, hrEq⟩ := Finset.mem_image.mp hmem
      cases hrEq
  obtain ⟨D, e, hBD, hfix, hassign, hcard⟩ :=
    Kakeya.Ninety21.extend_matching_to_bijection
      (P := Reg ⊕ Exc) (T := T ⊕ Exc)
      (paperSelectedExtended μ tubes n s m) σ hσ hOutside
  refine ⟨D, e, hBD, hfix, ?_, ?_, hcard⟩
  · intro p
    refine ⟨σ₀ p, ?_, (hgood p).1, (hgood p).2⟩
    simpa [σ] using hassign (Sum.inl p)
  · intro p
    simpa [σ] using hassign (Sum.inr p)

/-- The extended label set of the Theorem 4.6 equivalence. -/
noncomputable def paper46LabelSet
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    Finset (PaperExtendedLabel μ tubes n s m) :=
  Classical.choose (exists_paper46_hall_equiv μ tubes n s m a)

noncomputable def hallEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    ({r : PaperExtendedLabel μ tubes n s m //
      r ∈ paperSelectedExtended μ tubes n s m} ⊕
      (PaperRegularLabel μ tubes n s m ⊕
        PaperExceptionalLabel μ tubes n s m)) ≃
      {r : PaperExtendedLabel μ tubes n s m //
        r ∈ paper46LabelSet μ tubes n s m a} :=
  Classical.choose (Classical.choose_spec
    (exists_paper46_hall_equiv μ tubes n s m a))

/-- Properties follow from the same witness selected by hallEquiv. -/
theorem hallEquiv_selected_fixed
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (r : {r : PaperExtendedLabel μ tubes n s m //
      r ∈ paperSelectedExtended μ tubes n s m}) :
    (hallEquiv μ tubes n s m a (Sum.inl r)).val = r.val := by
  have h := (Classical.choose_spec (Classical.choose_spec
    (exists_paper46_hall_equiv μ tubes n s m a))).2.1 r
  exact h

theorem hallEquiv_exceptional_auxiliary
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : PaperExceptionalLabel μ tubes n s m) :
    (hallEquiv μ tubes n s m a (Sum.inr (Sum.inr p))).val =
      (Sum.inr p : PaperExtendedLabel μ tubes n s m) := by
  have h := (Classical.choose_spec (Classical.choose_spec
    (exists_paper46_hall_equiv μ tubes n s m a))).2.2.2.1 p
  exact h

theorem hallEquiv_regular_nonintersecting
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : PaperRegularLabel μ tubes n s m) :
    ∃ r : T,
      (hallEquiv μ tubes n s m a (Sum.inr (Sum.inl p))).val = Sum.inl r ∧
      r ∉ s.B m ∧
      ¬(s.retainedPiece m (Sum.inr p.val) ∩ tubes r).Nonempty := by
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_paper46_hall_equiv μ tubes n s m a))).2.2.1 p


/-! ## Regular representative indices -/

/-- The original tube index assigned to a regular piece by Theorem 4.6. -/
noncomputable def paper46RegularIndex
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : PaperRegularLabel μ tubes n s m) : T :=
  Classical.choose (hallEquiv_regular_nonintersecting μ tubes n s m a p)

theorem paper46RegularIndex_spec
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : PaperRegularLabel μ tubes n s m) :
    (hallEquiv μ tubes n s m a (Sum.inr (Sum.inl p))).val =
      Sum.inl (paper46RegularIndex μ tubes n s m a p) ∧
    paper46RegularIndex μ tubes n s m a p ∉ s.B m ∧
    ¬(s.retainedPiece m (Sum.inr p.val) ∩
      tubes (paper46RegularIndex μ tubes n s m a p)).Nonempty :=
  Classical.choose_spec (hallEquiv_regular_nonintersecting μ tubes n s m a p)

/-- Distinct regular pieces have distinct representative indices. -/
theorem paper46RegularIndex_injective
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    Function.Injective (paper46RegularIndex μ tubes n s m a) := by
  intro p p' h
  have hp := (paper46RegularIndex_spec μ tubes n s m a p).1
  have hp' := (paper46RegularIndex_spec μ tubes n s m a p').1
  have he : hallEquiv μ tubes n s m a (Sum.inr (Sum.inl p)) =
      hallEquiv μ tubes n s m a (Sum.inr (Sum.inl p')) := by
    apply Subtype.ext
    rw [hp, hp', h]
  have he' := (hallEquiv μ tubes n s m a).injective he
  have hreg : (Sum.inl p : PaperRegularLabel μ tubes n s m ⊕
      PaperExceptionalLabel μ tubes n s m) = Sum.inl p' :=
    Sum.inr.inj he'
  exact Sum.inl.inj hreg

/-- The image of the regular pieces under their representative assignment. -/
noncomputable def paper46RegularIndices
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) : Finset T := by
  classical
  exact Finset.univ.image (paper46RegularIndex μ tubes n s m a)

/-- Equivalence between regular pieces and their representative indices. -/
noncomputable def paper46RegularIndexEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    PaperRegularLabel μ tubes n s m ≃
      {r : T // r ∈ paper46RegularIndices μ tubes n s m a} := by
  classical
  let f : PaperRegularLabel μ tubes n s m →
      {r : T // r ∈ paper46RegularIndices μ tubes n s m a} :=
    fun p => ⟨paper46RegularIndex μ tubes n s m a p,
      Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p p' h
    apply paper46RegularIndex_injective μ tubes n s m a
    exact congrArg Subtype.val h
  · intro r
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp r.property
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp

theorem paper46RegularIndices_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    (paper46RegularIndices μ tubes n s m a).card =
      (paperRegularPieces μ tubes n s m).card := by
  classical
  have h := Fintype.card_congr (paper46RegularIndexEquiv μ tubes n s m a)
  simpa only [Fintype.card_coe] using h.symm

/-- Assign an original tube to a representative of a regular piece it intersects, when one
    exists. -/
noncomputable def paper46OriginalTubeMapReg
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (t : T) : Option {r : T //
      r ∈ paper46RegularIndices μ tubes n s m a} := by
  classical
  exact if h : ∃ p : PaperRegularLabel μ tubes n s m,
      (s.retainedPiece m (Sum.inr p.val) ∩ tubes t).Nonempty
    then some (paper46RegularIndexEquiv μ tubes n s m a (Classical.choose h))
    else none

/-- Bound the regular-piece count using lower bounds on original-tube fibers. -/
theorem paper46_regular_count_of_fibers
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (hFiberLower : ∀ r : {r : T //
      r ∈ paper46RegularIndices μ tubes n s m a},
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s m a ell = some r
          then (1 : ℝ) else 0) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperRegularPieces μ tubes n s m).card : ℝ) ≤
        (Fintype.card T : ℝ) := by
  classical
  have hf := paper_double_count_fibers
    (paper46OriginalTubeMapReg μ tubes n s m a)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    hFiberLower
  simpa only [Fintype.card_coe, paper46RegularIndices_card] using hf

end Kakeya.Ninety21
