module
public import Kakeya.Ninety21Theorem46Hall

/-!
# Theorem 4.6 reindexing in the analytic endpoint

The SAME retained source sets are transported by the paper's Theorem 4.6
bijection into the extended representative labels `T ⊕ P_exc`. The original
`T` contains only the N original tubes, never auxiliary labels.

The 4.6 matching is a HIGH-LEVEL construction (q >= 8). It cannot be used
at q = 1, 2, 4. The small-level count uses the existing Theorem 4.2
bijection only for its cardinality bound; the single source mass sum is
unchanged at every level.

The ONLY NEW INCIDENCE hypothesis for the large levels is `hFiberLower`,
which counts original-tube fibers of the REGULAR Theorem 4.6 labels. The
exceptional-piece contribution is left visible in the analytic estimate:
it has NOT been bounded by the desired geometry and is not replaced with
an unjustified numerical assumption.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- The original selected indices, embedded into the auxiliary-capable
    label type. -/
noncomputable def paper46SelectedSourceEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
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

/-- Partition the original remaining labels into the ACTUAL regular and
    exceptional pieces. This is an equivalence, not a selection or a loss of
    any piece. -/
noncomputable def paper46RemainingSourceEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
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

/-- The precise change of source labels before applying Theorem 4.6.
    Old source labels: selected originals ⊕ ALL remaining pieces.
    New source labels: selected extended ⊕ (regular ⊕ exceptional). -/
noncomputable def paper46SourceEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃
    ({r : PaperExtendedLabel μ tubes n s m //
        r ∈ paperSelectedExtended μ tubes n s m} ⊕
      (PaperRegularLabel μ tubes n s m ⊕
        PaperExceptionalLabel μ tubes n s m)) :=
  Equiv.sumCongr (paper46SelectedSourceEquiv μ tubes n s m)
    (paper46RemainingSourceEquiv μ tubes n s m)

/-- The actual source-piece-to-representative equivalence; its *second*
    factor is the NONINTERSECTING Theorem 4.6 `hallEquiv`. -/
noncomputable def paper46AnalyticEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃
    {r : PaperExtendedLabel μ tubes n s m //
      r ∈ paper46LabelSet μ tubes n s m a} :=
  (paper46SourceEquiv μ tubes n s m).trans (hallEquiv μ tubes n s m a)

/-- The exact, unchanged retained set represented by an extended label.
    Auxiliary labels index their corresponding exceptional SOURCE pieces;
    they are not interpreted as original tube geometries. -/
noncomputable def paper46AnalyticPiece
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (r : PaperExtendedLabel μ tubes n s m) : Set X :=
  if h : r ∈ paper46LabelSet μ tubes n s m a then
    s.sourcePiece m ((paper46AnalyticEquiv μ tubes n s m a).symm ⟨r,h⟩)
  else ∅

theorem paper46AnalyticPiece_at_equiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (p : {r : T // r ∈ s.B m} ⊕ {k : K // k ∈ s.P m}) :
    paper46AnalyticPiece μ tubes n s m a
      (paper46AnalyticEquiv μ tubes n s m a p).val =
      s.sourcePiece m p := by
  classical
  simp [paper46AnalyticPiece]

/-- Exact mass transport, now over the auxiliary-capable Theorem 4.6 labels.
    No auxiliary tube enters any incidence count or physical tube measure. -/
theorem paper46_analytic_mass_sum
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m) :
    (∑ r ∈ paper46LabelSet μ tubes n s m a,
      Kakeya.Conditional.mass μ (paper46AnalyticPiece μ tubes n s m a r)) =
    ∑ p, Kakeya.Conditional.mass μ (s.sourcePiece m p) := by
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

/-- The new extended label set counts EXACTLY the same retained pieces. -/
theorem paper46_analytic_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
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
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (a : Paper46ConstructionData μ tubes n s m)
    (r : PaperExtendedLabel μ tubes n s m)
    (hr : r ∈ paper46LabelSet μ tubes n s m a) :
    Kakeya.Conditional.mass μ (paper46AnalyticPiece μ tubes n s m a r) ≤
      s.C * s.deltaPow * s.radius m := by
  classical
  simpa [paper46AnalyticPiece, hr] using
    s.hVolume m ((paper46AnalyticEquiv μ tubes n s m a).symm ⟨r, hr⟩)

/-- Greedy capture on the original source sets; relabel by Theorem 4.6
    *after* capture. This has precisely the same Q, retained sets, and mass. -/
theorem paper46_analytic_capture
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
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
    (s.sourcePiece m) (fun _ => Set.univ) Finset.univ
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) (c.hScaleLe m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m)
    (c.hUnionMeasurable m) (c.hUnionSubset m) (c.hStep m)
    (by simpa using c.hPieceMeasurable m)
    (by simpa using c.hCover m)
  rw [paper46_analytic_mass_sum μ tubes n s m a]
  simpa using h

/-- Large-level distinct-representative count, derived from lower ORIGINAL-
    tube fibers of the REGULAR representatives and retaining the exceptional
    correction. In particular there is NO hPaperRow, TubeWiseUnique, or
    |P| <= |B| premise. -/
theorem paper46_analytic_count_with_exceptional
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
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


/-- The sole new incidence condition, packaged together with the existing
    Theorem 4.6 HIGH-LEVEL construction. The constructor's regular-cardinality
    hypothesis is still an upstream geometric obligation; this structure does
    not prove it. There is no additional row/parent uniqueness hypothesis. -/
structure Paper46LargeLevelInputs
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n) where
  construction : ∀ (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)),
    8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m →
      Paper46ConstructionData μ tubes n s m
  hFiberLower : ∀ (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hlarge : 8 ≤ Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (r : {r : T // r ∈ paper46RegularIndices μ tubes n s m
      (construction m hlarge)}),
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paper46OriginalTubeMapReg μ tubes n s m
            (construction m hlarge) ell = some r then (1 : ℝ) else 0

/-- The exceptional correction is a DEFINED finite sum, not a new
    hypothesis. It records exactly the work remaining for the packing
    estimates. The dyadic level type is finite. -/
noncomputable def paper46ExceptionalOverhead
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n) : ℝ :=
  ∑ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperExceptionalPieces μ tubes n s m).card : ℝ)

theorem paper46ExceptionalOverhead_nonneg
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n) :
    0 ≤ paper46ExceptionalOverhead μ tubes n s := by
  classical
  unfold paper46ExceptionalOverhead
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (Kakeya.Eighty4.dyadicScale_pos _ m).le
    (Nat.cast_nonneg _)

theorem paper46_exceptional_term_le_overhead
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
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

/-- On SMALL levels q<8, Theorem 4.6 is not applicable. The old Theorem 4.2
    equivalence implies only a cardinality estimate: there can be at most N
    source pieces. The ANALYTIC mass family itself is never replaced. -/
theorem paper46_small_source_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (s.B m).card + (s.P m).card ≤ Fintype.card T := by
  classical
  rw [← hall_reindexed_card μ tubes n s m]
  have h := Finset.card_le_card
    (Finset.subset_univ (hallReindexing μ tubes n s m).val)
  simpa using h

/-- Uniform all-level combinatorial budget with a visible exceptional
    correction. Only hFiberLower is a NEW incidence/counting input. -/
theorem paper46_all_level_source_count
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
        8 * (Fintype.card T : ℝ) +
          paper46ExceptionalOverhead μ tubes n s := by
  classical
  let q : ℝ := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  have hE := paper46_exceptional_term_le_overhead μ tubes n s m
  by_cases hlarge : 8 ≤ q
  · have hCount := paper46_analytic_count_with_exceptional μ tubes n s m
      (a.construction m hlarge) (a.hFiberLower m hlarge)
    have hCard := paper46_analytic_card μ tubes n s m
      (a.construction m hlarge)
    have hCardR : ((paper46LabelSet μ tubes n s m
        (a.construction m hlarge)).card : ℝ) =
        ((s.B m).card : ℝ) + ((s.P m).card : ℝ) := by
      exact_mod_cast hCard
    rw [hCardR] at hCount
    change q * (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
      8 * (Fintype.card T : ℝ) + paper46ExceptionalOverhead μ tubes n s
    have hN : 0 ≤ (Fintype.card T : ℝ) := Nat.cast_nonneg _
    linarith
  · have hq : q < 8 := by linarith
    have hcard := paper46_small_source_card μ tubes n s m
    have hcardR : ((s.B m).card : ℝ) + ((s.P m).card : ℝ) ≤
        (Fintype.card T : ℝ) := by
      exact_mod_cast hcard
    have hpos : 0 ≤ ((s.B m).card : ℝ) + ((s.P m).card : ℝ) := by
      positivity
    have hqBound : q * (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
        8 * (Fintype.card T : ℝ) := by
      calc
        _ ≤ 8 * (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) :=
          mul_le_mul_of_nonneg_right hq.le hpos
        _ ≤ 8 * (Fintype.card T : ℝ) :=
          mul_le_mul_of_nonneg_left hcardR (by norm_num)
    have hENonneg := paper46ExceptionalOverhead_nonneg μ tubes n s
    change q * (((s.B m).card : ℝ) + ((s.P m).card : ℝ)) ≤
      8 * (Fintype.card T : ℝ) + paper46ExceptionalOverhead μ tubes n s
    linarith

/-- Greedy capture for all levels, on precisely the ORIGINAL retained
    sets. At large levels its sum is *equal* to the Theorem 4.6 relabeled
    sum by `paper46_analytic_mass_sum`. -/
theorem paper46_source_capture
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Kakeya.Conditional.mass μ (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      (1 / (1 - Real.exp (-1))) *
        ∑ p, Kakeya.Conditional.mass μ (s.sourcePiece m p) := by
  classical
  have h := Kakeya.Eighty4.mass_capture_from_greedy_union
    μ (Kakeya.Eighty4.concreteDyadicBand tubes m) (c.Q m)
    (s.sourcePiece m) (fun _ => Set.univ) Finset.univ
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) (Fintype.card T : ℝ)
    (Kakeya.Eighty4.dyadicScale_pos _ m) (c.hScaleLe m)
    (Kakeya.Eighty4.concreteDyadicBand_measurable tubes hT m)
    (c.hUnionMeasurable m) (c.hUnionSubset m) (c.hStep m)
    (by simpa using c.hPieceMeasurable m)
    (by simpa using c.hCover m)
  simpa using h

/-- The dyadic analytic level budget is now connected to the Theorem 4.6
    count at large levels, and to the valid small-level count otherwise.
    The exceptional correction is explicit; no row uniqueness or extra
    incidence hypothesis is silently used. -/
theorem paper46_analytic_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
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
    have hc := paper46_all_level_source_count μ tubes n s a m
    simpa [q, U, E, Fintype.card_sum] using hc
  have hVolume : ∀ p ∈ (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m})),
        Kakeya.Conditional.mass μ (s.sourcePiece m p) ≤ v := by
    intro p hp
    exact s.hVolume m p
  have hCapture : Kakeya.Conditional.mass μ
      (Kakeya.Eighty4.concreteDyadicBand tubes m) ≤
      H * ∑ p, Kakeya.Conditional.mass μ (s.sourcePiece m p) := by
    by_cases hlarge : 8 ≤ q
    · have h := paper46_analytic_capture μ tubes n s c hT m
        (a.construction m hlarge)
      rw [paper46_analytic_mass_sum μ tubes n s m
        (a.construction m hlarge)] at h
      exact h
    · exact paper46_source_capture μ tubes n s c hT m
  have hBudget := localized_level_bound
    (Finset.univ : Finset
      ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}))
    (fun p => Kakeya.Conditional.mass μ (s.sourcePiece m p))
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
theorem paper46_analytic_uniform_level_budget
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i))
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
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
  have hLevel := paper46_analytic_level_budget μ tubes n s c a hT m
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

/-- Fully connected ANALYTIC endpoint through the Theorem 4.6 extended
    reindexing at q>=8. The exceptional geometric cost remains displayed,
    rather than being replaced by a false 4N count. No hypothesis beyond
    the regular original-tube lower fibers has been added to the counting
    argument. -/
theorem full_conditional_kakeya_moment_of_paper46
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        ((1 / (1 - Real.exp (-1))) * s.C *
          (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
            s.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  classical
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) := by
    apply div_nonneg
    · norm_num
    · linarith
  have h := Kakeya.Eighty9.logarithmic_moment_from_level_budgets μ tubes
    ((1 : ℝ) / ((n : ℝ) - 1))
    ((1 / (1 - Real.exp (-1))) * s.C *
      (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
        s.radiusCap)
    ha hT (paper46_analytic_uniform_level_budget μ tubes n s c a hT)
  rw [(Kakeya.Conditional.dimension_exponents n hn).1] at h
  exact h

/-- Norm-form companion of the moment endpoint, with the same exact
    exceptional correction. -/
theorem full_conditional_kakeya_of_paper46
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : SourceGreedyAtLevels μ tubes n s)
    (a : Paper46LargeLevelInputs μ tubes n s)
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        ((1 / (1 - Real.exp (-1))) * s.C *
          (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
            s.radiusCap) *
          ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
            (((n : ℝ) - 1) / (n : ℝ)) := by
  exact Kakeya.Eighty9.logarithmic_norm_from_level_budgets μ tubes n hn
    ((1 / (1 - Real.exp (-1))) * s.C *
      (8 * s.Z + paper46ExceptionalOverhead μ tubes n s * s.deltaPow) *
        s.radiusCap) hT
    (paper46_analytic_uniform_level_budget μ tubes n s c a hT)

end Kakeya.Ninety21
