module
public import Kakeya.Ninety21RegularBudget

/-!
# Theorem 4.6 analytic endpoint

The Theorem 4.6 bijection relabels retained sets by original and
exceptional auxiliary labels. Their mass sum is preserved. At levels q ≥ 8,
regular original-tube fibers give the counting bound with an exceptional
contribution. Levels q < 8 use the finite ambient mass estimate.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- The original selected indices, embedded into the auxiliary-capable
    label type. -/
noncomputable def paper46SelectedRetainedEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    {r : T // r ∈ s.B m} ≃
      {r : PaperExtendedLabel μ tubes n s m //
        r ∈ paperSelectedExtended μ tubes n s m} := by
  classical
  let f : {r : T // r ∈ s.B m} →
      {r : PaperExtendedLabel μ tubes n s m //
        r ∈ paperSelectedExtended μ tubes n s m} :=
    fun p => ⟨Sum.inl p.val,
      Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact Sum.inl.inj (congrArg Subtype.val h)
  · intro y
    obtain ⟨r, hr, hre⟩ := Finset.mem_image.mp y.property
    refine ⟨⟨r, hr⟩, ?_⟩
    apply Subtype.ext
    exact hre

/-- Partition the remaining retained labels into regular and exceptional pieces. -/
noncomputable def paper46RemainingRetainedEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    {p : K // p ∈ s.P m} ≃
      (PaperRegularLabel μ tubes n s m ⊕
        PaperExceptionalLabel μ tubes n s m) := by
  classical
  let f : (PaperRegularLabel μ tubes n s m ⊕
        PaperExceptionalLabel μ tubes n s m) →
        {p : K // p ∈ s.P m} :=
    Sum.elim (fun p => p.val) (fun p => p.val)
  have hdisj := (paper_regular_exceptional_partition μ tubes n s m).1
  have hcover := (paper_regular_exceptional_partition μ tubes n s m).2
  have hinj : Function.Injective f := by
    intro u v huv
    cases u with
    | inl p =>
      cases v with
      | inl p' =>
        exact congrArg Sum.inl (Subtype.ext huv)
      | inr p' =>
        exfalso
        have hval : p.val = p'.val := huv
        have hpr : p'.val ∈ paperRegularPieces μ tubes n s m := by
          simpa only [hval] using p.property
        exact (Finset.disjoint_left.mp hdisj) hpr p'.property
    | inr p =>
      cases v with
      | inl p' =>
        exfalso
        have hval : p.val = p'.val := huv
        have hpe : p'.val ∈ paperExceptionalPieces μ tubes n s m := by
          simpa only [hval] using p.property
        exact (Finset.disjoint_left.mp hdisj) p'.property hpe
      | inr p' =>
        exact congrArg Sum.inr (Subtype.ext huv)
  have hsurj : Function.Surjective f := by
    intro p
    have hp : p ∈ paperRegularPieces μ tubes n s m ∪
        paperExceptionalPieces μ tubes n s m := by
      rw [hcover]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hp with hr | he
    · exact ⟨Sum.inl ⟨p, hr⟩, rfl⟩
    · exact ⟨Sum.inr ⟨p, he⟩, rfl⟩
  exact (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm

/-- Relabel selected indices and partition the remaining retained labels. -/
noncomputable def paper46RetainedEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃
    ({r : PaperExtendedLabel μ tubes n s m //
        r ∈ paperSelectedExtended μ tubes n s m} ⊕
      (PaperRegularLabel μ tubes n s m ⊕
        PaperExceptionalLabel μ tubes n s m)) :=
  Equiv.sumCongr (paper46SelectedRetainedEquiv μ tubes n s m)
    (paper46RemainingRetainedEquiv μ tubes n s m)

/-- Compose the retained-label partition with the Theorem 4.6 equivalence. -/
noncomputable def paper46AnalyticEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃
    {r : PaperExtendedLabel μ tubes n s m //
      r ∈ paper46LabelSet μ tubes n s m a} :=
  (paper46RetainedEquiv μ tubes n s m).trans (hallEquiv μ tubes n s m a)

/-- The retained set represented by an extended label. -/
noncomputable def paper46AnalyticPiece
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (r : PaperExtendedLabel μ tubes n s m) : Set X :=
  if h : r ∈ paper46LabelSet μ tubes n s m a then
    s.retainedPiece m ((paper46AnalyticEquiv μ tubes n s m a).symm ⟨r,h⟩)
  else ∅

theorem paper46AnalyticPiece_at_equiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : {r : T // r ∈ s.B m} ⊕ {k : K // k ∈ s.P m}) :
    paper46AnalyticPiece μ tubes n s m a
      (paper46AnalyticEquiv μ tubes n s m a p).val =
      s.retainedPiece m p := by
  classical
  simp [paper46AnalyticPiece]

/-- The Theorem 4.6 relabeling preserves the sum of retained masses. -/
theorem paper46_analytic_mass_sum
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    (∑ r ∈ paper46LabelSet μ tubes n s m a,
      Kakeya.Conditional.mass μ (paper46AnalyticPiece μ tubes n s m a r)) =
    ∑ p, Kakeya.Conditional.mass μ (s.retainedPiece m p) := by
  classical
  let e := paper46AnalyticEquiv μ tubes n s m a
  have h := Equiv.sum_comp e
    (fun l => Kakeya.Conditional.mass μ
      (paper46AnalyticPiece μ tubes n s m a l.val))
  dsimp [e] at h
  simp only [paper46AnalyticPiece_at_equiv] at h
  calc
    _ = ∑ r ∈ (paper46LabelSet μ tubes n s m a).attach,
        Kakeya.Conditional.mass μ
          (paper46AnalyticPiece μ tubes n s m a r.val) :=
      (Finset.sum_attach (paper46LabelSet μ tubes n s m a)
        (fun r => Kakeya.Conditional.mass μ
          (paper46AnalyticPiece μ tubes n s m a r))).symm
    _ = _ := h.symm

/-- The extended label set has the cardinality of the retained family. -/
theorem paper46_analytic_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    (paper46LabelSet μ tubes n s m a).card =
      (s.B m).card + (s.P m).card := by
  classical
  have h := Fintype.card_congr (paper46AnalyticEquiv μ tubes n s m a)
  simpa only [Fintype.card_sum, Fintype.card_coe] using h.symm

/-- The geometric volume estimate transfers to the new representative labels
    by the inverse equivalence. -/
theorem paper46_analytic_piece_volume
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (r : PaperExtendedLabel μ tubes n s m)
    (hr : r ∈ paper46LabelSet μ tubes n s m a) :
    Kakeya.Conditional.mass μ (paper46AnalyticPiece μ tubes n s m a r) ≤
      s.C * s.deltaPow * s.radius m := by
  classical
  simpa [paper46AnalyticPiece, hr] using
    s.hVolume m ((paper46AnalyticEquiv μ tubes n s m a).symm ⟨r, hr⟩)

/-- Greedy capture on the original retained sets; relabel by Theorem 4.6
    *after* capture. This has precisely the same Q, retained sets, and mass. -/
theorem paper46_analytic_capture
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) *
        ∑ r ∈ paper46LabelSet μ tubes n s m a,
          Kakeya.Conditional.mass μ (paper46AnalyticPiece μ tubes n s m a r) := by
  classical
  have h := Kakeya.Eighty4.mass_capture_from_greedy_union
    μ (Kakeya.Eighty4.concreteDyadicBand tubes m) (c.Q m)
    (s.retainedPiece m) (fun _ => Set.univ) Finset.univ
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) (c.hScaleLe m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m)
    (c.hUnionMeasurable m) (c.hUnionSubset m) (c.hStep m)
    (by simpa using c.hPieceMeasurable m)
    (by simpa using c.hCover m)
  rw [paper46_analytic_mass_sum μ tubes n s m a]
  simpa using h

/-- Count representatives using regular original-tube fibers and the exceptional-piece
    contribution. -/
theorem paper46_analytic_count_with_exceptional
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
      ((paper46LabelSet μ tubes n s m a).card : ℝ) ≤
        3 * (Fintype.card T : ℝ) +
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
            ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
  classical
  have hReg := paper46_regular_count_of_fibers μ tubes n s m a hFiberLower
  have hGreedy := s.hGreedy m
  have hPart : ((s.P m).card : ℝ) =
      ((paperRegularPieces μ tubes n s m).card : ℝ) +
        ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
    exact_mod_cast (paper_regular_exceptional_card μ tubes n s m).symm
  have hCard : ((paper46LabelSet μ tubes n s m a).card : ℝ) =
      ((s.B m).card : ℝ) + ((s.P m).card : ℝ) := by
    exact_mod_cast paper46_analytic_card μ tubes n s m a
  rw [hCard, hPart]
  nlinarith


/-- Theorem 4.6 constructions and regular-fiber lower bounds above an analytic cutoff. -/
structure Paper46LargeLevelInputs
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) where
  cutoff : ℝ
  hCutoff : 8 ≤ cutoff
  construction : ∀ (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)),
    cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m →
      Paper46ConstructionData μ tubes n s m
  hFiberLower : ∀ (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (r : {r : T // r ∈ paper46RegularIndices μ tubes n s m
      (construction m hlarge)}),
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s m
            (construction m hlarge) ell = some r then (1 : ℝ) else 0

/-- Build the endpoint inputs from tube–ball counting and regular-fiber bounds. -/
noncomputable def paper46LargeLevelInputs_of_tube_ball_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (hPairInjective : ∀ m, Function.Injective
      (fun p : {k : K // k ∈ s.P m} =>
        (s.parent m p, s.sourceBall m (Sum.inr p))))
    (hLarge : ∀ m,
      8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m →
      (8 : ℝ) * (s.ballPackingConstant *
        (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
          ((1 : ℝ) / ((n : ℝ) - 1))) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (hFiberLower : ∀ m
      (hq : 8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
      (r : {r : T // r ∈ paper46RegularIndices μ tubes n s.toRetainedDyadicData m
        (paper46Construction_of_dyadic_tube_ball_count μ tubes n s m hq
          (hPairInjective m) (hLarge m hq))}),
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s.toRetainedDyadicData m
            (paper46Construction_of_dyadic_tube_ball_count μ tubes n s m hq
              (hPairInjective m) (hLarge m hq)) ell = some r
          then (1 : ℝ) else 0) :
    Paper46LargeLevelInputs μ tubes n s.toRetainedDyadicData where
  cutoff := 8
  hCutoff := le_rfl
  construction m hq := paper46Construction_of_dyadic_tube_ball_count
    μ tubes n s m hq (hPairInjective m) (hLarge m hq)
  hFiberLower := hFiberLower

/-- Endpoint inputs for pair-indexed pieces above the packing cutoff. -/
noncomputable def paper46LargeLevelInputs_of_pair_indexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) (hn : 3 ≤ n)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (hFiberLower : ∀ m
      (hq : paper46Cutoff s.ballPackingConstant ≤
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
      (r : {r : T // r ∈ paper46RegularIndices μ tubes n s.toRetainedDyadicData m
        (paper46Construction_of_pair_indexing_at_cutoff μ tubes n hn s indexing m hq)}),
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s.toRetainedDyadicData m
            (paper46Construction_of_pair_indexing_at_cutoff μ tubes n hn s indexing m hq)
              ell = some r
          then (1 : ℝ) else 0) :
    Paper46LargeLevelInputs μ tubes n s.toRetainedDyadicData where
  cutoff := paper46Cutoff s.ballPackingConstant
  hCutoff := le_max_left _ _
  construction m hq :=
    paper46Construction_of_pair_indexing_at_cutoff μ tubes n hn s indexing m hq
  hFiberLower := hFiberLower

/-- The sum of dyadically weighted exceptional-piece counts. -/
noncomputable def paper46ExceptionalOverhead
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) : ℝ :=
  ∑ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s m).card : ℝ)

theorem paper46ExceptionalOverhead_nonneg
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) :
    0 ≤ paper46ExceptionalOverhead μ tubes n s := by
  classical
  unfold paper46ExceptionalOverhead
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (Kakeya.Eighty4.dyadicScale_pos _ m).le
    (Nat.cast_nonneg _)

theorem paper46_exceptional_term_le_overhead
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s m).card : ℝ) ≤
        paper46ExceptionalOverhead μ tubes n s := by
  classical
  unfold paper46ExceptionalOverhead
  let f : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ :=
    fun j => Kakeya.Eighty4.dyadicScale (Fintype.card T) j *
      ((paperExceptionalPieces μ tubes n s j).card : ℝ)
  change f m ≤ ∑ j, f j
  exact Finset.single_le_sum (s := Finset.univ) (f := f)
    (by
      intro j hj
      exact mul_nonneg (Kakeya.Eighty4.dyadicScale_pos _ j).le
        (Nat.cast_nonneg _))
    (Finset.mem_univ m)

/-- Retained cardinality budget at levels where Theorem 4.6 applies. -/
theorem paper46_large_level_retained_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
        8 * (Fintype.card T : ℝ) + paper46ExceptionalOverhead μ tubes n s := by
  classical
  have hE := paper46_exceptional_term_le_overhead μ tubes n s m
  have hCount := paper46_analytic_count_with_exceptional μ tubes n s m
    (a.construction m hlarge) (a.hFiberLower m hlarge)
  have hCardR : ((paper46LabelSet μ tubes n s m
      (a.construction m hlarge)).card : ℝ) =
      ((s.B m).card : ℝ) + ((s.P m).card : ℝ) := by
    exact_mod_cast paper46_analytic_card μ tubes n s m (a.construction m hlarge)
  rw [hCardR] at hCount
  have hN : 0 ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
  linarith

/-- Direct finite-measure bound for small dyadic levels. -/
theorem paper46_small_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (alpha : ℝ) (ha : 0 ≤ alpha)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (cutoff : ℝ)
    (hsmall : Kakeya.Eighty4.dyadicScale (Fintype.card T) m < cutoff) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^ (1 + alpha) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        cutoff ^ (1 + alpha) * Kakeya.Conditional.mass μ Set.univ := by
  classical
  have hmass : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        Kakeya.Conditional.mass μ Set.univ := by
    unfold Kakeya.Conditional.mass
    apply integral_mono_ae
      (Kakeya.Conditional.chi_integrable μ _
        (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m))
      (Kakeya.Conditional.chi_integrable μ Set.univ MeasurableSet.univ)
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ Kakeya.Eighty4.concreteDyadicBand tubes m <;>
      simp [Kakeya.Conditional.chi, hx]
  have hpow := Real.rpow_le_rpow
    (Kakeya.Eighty4.dyadicScale_pos (Fintype.card T) m).le hsmall.le
    (show 0 ≤ 1 + alpha by linarith)
  have hnonneg : 0 ≤ Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) :=
    integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg _ x)
  exact mul_le_mul hpow hmass hnonneg (Real.rpow_nonneg
    ((Kakeya.Eighty4.dyadicScale_pos _ m).le.trans hsmall.le) _)

/-- Greedy mass capture for the retained sets at every dyadic level. -/
theorem paper46_retained_capture
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) *
        ∑ p, Kakeya.Conditional.mass μ (s.retainedPiece m p) := by
  classical
  have h := Kakeya.Eighty4.mass_capture_from_greedy_union
    μ (Kakeya.Eighty4.concreteDyadicBand tubes m) (c.Q m)
    (s.retainedPiece m) (fun _ => Set.univ) Finset.univ
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) (c.hScaleLe m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m)
    (c.hUnionMeasurable m) (c.hUnionSubset m) (c.hStep m)
    (by simpa using c.hPieceMeasurable m)
    (by simpa using c.hCover m)
  simpa using h

/-- The large-level analytic budget with its exceptional contribution. -/
theorem paper46_analytic_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * s.C *
        (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
          s.radius m := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let H : ℝ := 1 / (1 - Real.exp (-1))
  let E : ℝ := paper46ExceptionalOverhead μ tubes n s
  let U : ℝ := 8 * (Fintype.card T : ℝ) + E
  let v : ℝ := s.C * s.deltaPow * s.radius m
  have hH : 0 ≤ H := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hv : 0 ≤ v :=
    mul_nonneg (mul_nonneg s.hC s.hDeltaPow) (s.hRadiusNonneg m)
  have hCount : q *
      ((Finset.univ : Finset
        ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m})).card : ℝ) ≤
        (1 : ℝ) * U := by
    have hc := paper46_large_level_retained_count μ tubes n s a m hlarge
    simpa [q, U, E, Fintype.card_sum] using hc
  have hVolume : ∀ p ∈ (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m})),
        Kakeya.Conditional.mass μ (s.retainedPiece m p) ≤ v := by
    intro p hp
    exact s.hVolume m p
  have hCapture : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * ∑ p, Kakeya.Conditional.mass μ (s.retainedPiece m p) := by
    have h := paper46_analytic_capture μ tubes n s c hT m
      (a.construction m hlarge)
    rw [paper46_analytic_mass_sum μ tubes n s m
      (a.construction m hlarge)] at h
    exact h
  have hBudget := localized_level_bound
    (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}))
    (fun p => Kakeya.Conditional.mass μ (s.retainedPiece m p))
    (Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m))
    H v q U 1 hH hv (Kakeya.Eighty4.dyadicScale_pos _ m).le
    hCapture hVolume hCount
  have hCoeff : 0 ≤ H * s.C * s.radius m :=
    mul_nonneg (mul_nonneg hH s.hC) (s.hRadiusNonneg m)
  have hNorm : 8 * ((Fintype.card T : ℝ) * s.deltaPow) +
      E * s.deltaPow ≤ 8 * s.Z + E * s.deltaPow := by
    have := mul_le_mul_of_nonneg_left s.hNormalization (by norm_num : (0:ℝ) ≤ 8)
    linarith
  change q * Kakeya.Conditional.mass μ
    (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * s.C * (8 * s.Z + E * s.deltaPow) * s.radius m
  calc
    _ ≤ H * U * v := by simpa [U] using hBudget
    _ = (H * s.C * s.radius m) *
        (8 * ((Fintype.card T : ℝ) * s.deltaPow) + E * s.deltaPow) := by
          dsimp [U, v]
          ring
    _ ≤ (H * s.C * s.radius m) * (8 * s.Z + E * s.deltaPow) :=
      mul_le_mul_of_nonneg_left hNorm hCoeff
    _ = H * s.C * (8 * s.Z + E * s.deltaPow) * s.radius m := by ring

/-- Uniform bound compatible with the repository's logarithmic dyadic
    summation theorem. -/
theorem paper46_large_uniform_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) * s.C *
        (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
          s.radiusCap := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  let alpha : ℝ := (1 : ℝ) / ((n : ℝ) - 1)
  let W : ℝ := (1 / (1 - Real.exp (-1))) * s.C *
    (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow)
  have hq : 0 < q := Kakeya.Eighty4.dyadicScale_pos _ m
  have hqa : 0 ≤ q ^ alpha := Real.rpow_nonneg hq.le _
  have hpow : q ^ (1 + alpha) = q * q ^ alpha := by
    rw [Real.rpow_add hq 1 alpha, Real.rpow_one]
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hE := paper46ExceptionalOverhead_nonneg μ tubes n s
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hW : 0 ≤ W := by
    dsimp [W]
    apply mul_nonneg (mul_nonneg hH s.hC)
    exact add_nonneg (mul_nonneg (by norm_num) hZ)
      (mul_nonneg hE s.hDeltaPow)
  have hLevel := paper46_analytic_level_budget μ tubes n s c a hT m hlarge
  have hScaled := mul_le_mul_of_nonneg_left hLevel hqa
  have hCap := mul_le_mul_of_nonneg_left (s.hRadiusScale m) hW
  change q ^ (1 + alpha) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        W * s.radiusCap
  calc
    _ = (q ^ alpha) *
        (q * Kakeya.Conditional.mass μ
          (Kakeya.Eighty4.concreteDyadicBand tubes m)) := by
            rw [hpow]
            ring
    _ ≤ (q ^ alpha) * (W * s.radius m) := by
      simpa only [W] using hScaled
    _ = W * (q ^ alpha * s.radius m) := by ring
    _ ≤ W * s.radiusCap := hCap

/-- Combined coefficient for the large-level estimate and finite small-level mass. -/
noncomputable def paper46EndpointBudget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) (cutoff : ℝ := 8) : ℝ :=
  (1 / (1 - Real.exp (-1))) * s.C *
    (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) * s.radiusCap +
    cutoff ^ (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ Set.univ

/-- Uniform dyadic budget obtained by splitting at the analytic cutoff. -/
theorem paper46_analytic_uniform_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
        paper46EndpointBudget μ tubes n s a.cutoff := by
  have hmass : 0 ≤ Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    integral_nonneg (fun x => Kakeya.Conditional.chi_nonneg _ x)
  have hsmallNonneg : 0 ≤ a.cutoff ^ (1 + (1 : ℝ) / ((n : ℝ) - 1)) *
      Kakeya.Conditional.mass μ (Set.univ : Set X) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [a.hCutoff]) _) hmass
  have hZ : 0 ≤ s.Z :=
    (mul_nonneg (Nat.cast_nonneg _) s.hDeltaPow).trans s.hNormalization
  have hE := paper46ExceptionalOverhead_nonneg μ tubes n s
  have hH : 0 ≤ (1 : ℝ) / (1 - Real.exp (-1)) := by
    have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_nonneg (by norm_num) (sub_nonneg.mpr he.le)
  have hCap : 0 ≤ s.radiusCap := by
    exact (mul_nonneg (Real.rpow_nonneg
      (Kakeya.Eighty4.dyadicScale_pos _ m).le _) (s.hRadiusNonneg m)).trans
        (s.hRadiusScale m)
  have hlargeNonneg : 0 ≤ (1 / (1 - Real.exp (-1))) * s.C *
      (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
        s.radiusCap :=
    mul_nonneg (mul_nonneg (mul_nonneg hH s.hC)
      (add_nonneg (mul_nonneg (by norm_num) hZ)
        (mul_nonneg hE s.hDeltaPow))) hCap
  unfold paper46EndpointBudget
  by_cases hlarge : a.cutoff ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  · exact (paper46_large_uniform_level_budget μ tubes n s c a hT m hlarge).trans
      (le_add_of_nonneg_right hsmallNonneg)
  · have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
      apply div_nonneg (by norm_num)
      linarith
    exact (paper46_small_level_budget μ tubes ((1 : ℝ) / ((n : ℝ) - 1))
      ha hT m a.cutoff (lt_of_not_ge hlarge)).trans (le_add_of_nonneg_left hlargeNonneg)

/-- Moment estimate from the large-level construction and the small-level bound. -/
theorem full_conditional_kakeya_moment_of_paper46
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46EndpointBudget μ tubes n s a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg (by norm_num)
    linarith
  have h := Kakeya.Eighty9.logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1)) (paper46EndpointBudget μ tubes n s a.cutoff)
    ha hT (paper46_analytic_uniform_level_budget μ tubes n hn s c a hT)
  rw [(Kakeya.Conditional.dimension_exponents n hn).1] at h
  exact h

/-- Norm estimate with the combined large-level and small-level coefficient. -/
theorem full_conditional_kakeya_of_paper46
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : RetainedDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        paper46EndpointBudget μ tubes n s a.cutoff *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((n : ℝ) - 1) / (n : ℝ)) := by
  exact Kakeya.Eighty9.logarithmic_norm_from_level_budgets μ tubes n hn
    (paper46EndpointBudget μ tubes n s a.cutoff) hT
    (paper46_analytic_uniform_level_budget μ tubes n hn s c a hT)

end Kakeya.Ninety21
