module
public import Kakeya.Ninety21Endpoint
public import Kakeya.Ninety64TrimmedBijection

/-!
# Retained pieces, localization balls, and Hall reindexing

`RetainedDyadicData` supplies the retained family for the Theorem 4.6 endpoint.
`BallLocalizedDyadicData` adds localization balls and their tube-count bound.
`TrimmedHallDyadicData` adds the right-degree bound used by Theorem 4.2.
Hall relabeling preserves the retained sets and their mass sum.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]
variable {μ : Measure X} {tubes : T → Set X} {n : ℕ}

/-- Retained family indexed by selected labels and remaining piece labels. -/
structure RetainedDyadicData
    (μ : Measure X) (tubes : T → Set X) (n : ℕ) where
  B : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset T
  P : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → Finset K
  retainedPiece : ∀ m, ({r : T // r ∈ B m} ⊕ {p : K // p ∈ P m}) → Set X
  gain : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → T → Set X
  parent : ∀ m, {p : K // p ∈ P m} → T
  hParent : ∀ m p, parent m p ∈ B m
  hGainDisjoint : ∀ m i j, i ≠ j → Disjoint (gain m i) (gain m j)
  hNonempty : ∀ m s, (retainedPiece m s).Nonempty
  hTrimmed : ∀ m p,
    retainedPiece m (Sum.inr p) ⊆ tubes (parent m p) ∩ gain m (parent m p)
  hLevel : ∀ m s, retainedPiece m s ⊆ Kakeya.Eighty4.concreteDyadicBand tubes m
  radius : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℝ
  C : ℝ
  deltaPow : ℝ
  Z : ℝ
  radiusCap : ℝ
  hC : 0 ≤ C
  hDeltaPow : 0 ≤ deltaPow
  hRadiusNonneg : ∀ m, 0 ≤ radius m
  hGreedy : ∀ m, Kakeya.Eighty4.dyadicScale (Fintype.card T) m * (B m).card ≤
    2 * (Fintype.card T : ℝ)
  hVolume : ∀ m s, Kakeya.Conditional.mass μ (retainedPiece m s) ≤ C * deltaPow * radius m
  hNormalization : (Fintype.card T : ℝ) * deltaPow ≤ Z
  hRadiusScale : ∀ m,
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
      ((1 : ℝ) / ((n : ℝ) - 1)) * radius m ≤ radiusCap

/-- The original indexing notation, interpreted through the retained family. -/
@[inline] abbrev RetainedDyadicData.sourcePiece
    (s : RetainedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {r : T // r ∈ s.B m} ⊕ {k : K // k ∈ s.P m}) : Set X :=
  s.retainedPiece m p

/-- Retained pieces with localization balls and a tube–ball counting bound. -/
structure BallLocalizedDyadicData
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    extends RetainedDyadicData (K := K) μ tubes n where
  /-- Finite localization-ball family. -/
  ballCount : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ
  ball : ∀ m, Fin (ballCount m) → Set X
  sourceBall : ∀ m, ({r : T // r ∈ B m} ⊕ {p : K // p ∈ P m}) → Fin (ballCount m)
  hSourceBall : ∀ m s, retainedPiece m s ⊆ ball m (sourceBall m s)
  hBallOccupied : ∀ m i,
    (ball m i ∩ Kakeya.Eighty4.concreteDyadicBand tubes m).Nonempty
  ballPackingConstant : ℝ
  hBallPackingConstant : 0 ≤ ballPackingConstant
  /-- Number of localization balls meeting an original tube. -/
  hHallRight : ∀ m r,
    (∑ i : Fin (ballCount m),
      if (ball m i ∩ tubes r).Nonempty then (1 : ℝ) else 0) ≤
      ballPackingConstant * (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        ((1 : ℝ) / ((n : ℝ) - 1))

/-- Retained-set projection through ball localization. -/
@[inline] abbrev BallLocalizedDyadicData.sourcePiece
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {r : T // r ∈ s.B m} ⊕ {k : K // k ∈ s.P m}) : Set X :=
  s.retainedPiece m p

instance (μ : Measure X) (tubes : T → Set X) (n : ℕ) :
    Coe (BallLocalizedDyadicData (K := K) μ tubes n)
      (RetainedDyadicData (K := K) μ tubes n) where
  coe := BallLocalizedDyadicData.toRetainedDyadicData

/-- Coordinate identities for retained labels indexed by tube–ball pairs. -/
structure TubeBallPairIndexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n) : Prop where
  parent_eq : ∀ m p, s.parent m p = p.val.1
  sourceBall_eq : ∀ m p, (s.sourceBall m (Sum.inr p)).val = p.val.2

/-- The parent and localization ball determine a retained pair label. -/
theorem TubeBallPairIndexing.pair_injective
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := T × ℕ) μ tubes n)
    (indexing : TubeBallPairIndexing μ tubes n s)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Function.Injective (fun p : {k : T × ℕ // k ∈ s.P m} =>
      (s.parent m p, s.sourceBall m (Sum.inr p))) := by
  intro p p' h
  apply Subtype.ext
  apply Prod.ext
  · simpa only [indexing.parent_eq] using congrArg Prod.fst h
  · simpa only [indexing.sourceBall_eq] using
      congrArg (fun z : T × Fin (s.ballCount m) => z.2.val) h

/-- Additional right-degree bound for the intersecting Theorem 4.2 matching. -/
structure TrimmedHallDyadicData
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    extends BallLocalizedDyadicData (K := K) μ tubes n where
  hPieceHallRight : ∀ m r,
    (∑ s, if (retainedPiece m s ∩ tubes r).Nonempty then (1 : ℝ) else 0) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m

/-- Retained-set projection through the trimmed Hall data. -/
@[inline] abbrev TrimmedHallDyadicData.sourcePiece
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {r : T // r ∈ s.B m} ⊕ {k : K // k ∈ s.P m}) : Set X :=
  s.retainedPiece m p

instance (μ : Measure X) (tubes : T → Set X) (n : ℕ) :
    Coe (TrimmedHallDyadicData (K := K) μ tubes n)
      (RetainedDyadicData (K := K) μ tubes n) where
  coe := fun s => s.toBallLocalizedDyadicData.toRetainedDyadicData

/-- Hall matching of occupied localization balls under the tube–ball scale bound. -/
theorem exists_ball_hall_reindexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : BallLocalizedDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hScale : s.ballPackingConstant *
      (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m) :
    ∃ (D : Finset T) (e : Fin (s.ballCount m) ≃ {r : T // r ∈ D}),
      (∀ i, (s.ball m i ∩ tubes (e i).val).Nonempty) ∧
      D.card = Fintype.card (Fin (s.ballCount m)) := by
  classical
  apply Kakeya.Ninety64.theorem42_actual_piece_bijection
    (s.ball m) tubes
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (s.ballPackingConstant *
      (Kakeya.Eighty4.dyadicScale (Fintype.card T) m) ^
        ((1 : ℝ) / ((n : ℝ) - 1)))
    (Kakeya.Eighty4.dyadicScale_pos _ m) hScale
  · intro i
    obtain ⟨x, hxball, hxlevel⟩ := s.hBallOccupied m i
    have hlo := hxlevel.1
    rw [Kakeya.Eighty4.tubeMultiplicity_eq_count] at hlo
    have hsub : Finset.univ.filter (fun r : T => x ∈ tubes r) ⊆
        Finset.univ.filter (fun r : T => (s.ball m i ∩ tubes r).Nonempty) := by
      intro r hr
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨x, hxball, (Finset.mem_filter.mp hr).2⟩⟩
    have hc : ((Finset.univ.filter (fun r : T => x ∈ tubes r)).card : ℝ) ≤
        ((Finset.univ.filter (fun r : T =>
          (s.ball m i ∩ tubes r).Nonempty)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hlo.trans hc
  · intro r
    simpa [Finset.sum_boole] using s.hHallRight m r

/-- Construct the piece Hall bijection using the dyadic multiplicity lower bound. -/
theorem exists_hall_reindexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    ∃ (D : Finset T)
      (e : ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃ {r : T // r ∈ D}),
      (∀ p, (s.retainedPiece m p ∩ tubes (e p).val).Nonempty) ∧
      D.card = Fintype.card ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) := by
  classical
  apply Kakeya.Ninety64.theorem42_actual_piece_bijection
    (s.retainedPiece m) tubes
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    (Kakeya.Eighty4.dyadicScale_pos _ m) le_rfl
  · intro p
    obtain ⟨x, hx⟩ := s.hNonempty m p
    have hlo := (s.hLevel m p hx).1
    rw [Kakeya.Eighty4.tubeMultiplicity_eq_count] at hlo
    have hsub : Finset.univ.filter (fun r : T => x ∈ tubes r) ⊆
        Finset.univ.filter (fun r : T => (s.retainedPiece m p ∩ tubes r).Nonempty) := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hx, (Finset.mem_filter.mp hr).2⟩⟩
    have hc : ((Finset.univ.filter (fun r : T => x ∈ tubes r)).card : ℝ) ≤
        ((Finset.univ.filter (fun r : T =>
          (s.retainedPiece m p ∩ tubes r).Nonempty)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hlo.trans hc
  · intro r
    simpa [Finset.sum_boole] using s.hPieceHallRight m r

/-- A chosen Hall reindexing, retaining its geometric compatibility proof. -/
noncomputable def hallReindexing
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    {D : Finset T // ∃ e : ({r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) ≃
      {r : T // r ∈ D}, ∀ p, (s.retainedPiece m p ∩ tubes (e p).val).Nonempty} := by
  classical
  let h := exists_hall_reindexing μ tubes n s m
  refine ⟨Classical.choose h, ?_⟩
  obtain ⟨e, hh, _⟩ := Classical.choose_spec h
  exact ⟨e, hh⟩

noncomputable def hallEquiv42
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :=
  Classical.choose (hallReindexing μ tubes n s m).property

/-- The retained set indexed by the inverse Hall equivalence. -/
noncomputable def hallPiece
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) (l : T) : Set X :=
  if h : l ∈ (hallReindexing μ tubes n s m).val then
    s.retainedPiece m ((hallEquiv42 μ tubes n s m).symm ⟨l, h⟩) else ∅

/-- Hall reindexing preserves the total number of selected and remaining retained labels. -/
theorem hall_reindexed_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (hallReindexing μ tubes n s m).val.card = (s.B m).card + (s.P m).card := by
  classical
  have h := Fintype.card_congr (hallEquiv42 μ tubes n s m)
  simpa only [Fintype.card_sum, Fintype.card_coe] using h.symm

/-! ## Analytic data from Hall reindexing -/

/-- Construct analytic data from Hall reindexing, volume bounds, and the scaled count. -/
noncomputable def data_of_trimmed_hall
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (hTubeCount : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((hallReindexing μ tubes n s m).val.card : ℝ) ≤
          4 * (Fintype.card T : ℝ)) :
    SelectedIncidenceDyadicData (K := K) μ tubes n := by
  classical
  exact {
    B := s.B, P := s.P
    D := fun m => (hallReindexing μ tubes n s m).val
    e := hallEquiv42 μ tubes n s
    piece := hallPiece μ tubes n s
    radius := s.radius, C := s.C, deltaPow := s.deltaPow, Z := s.Z, radiusCap := s.radiusCap
    hC := s.hC, hDeltaPow := s.hDeltaPow, hRadiusNonneg := s.hRadiusNonneg
    hGreedy := s.hGreedy
    hTubeCount := hTubeCount
    hPieceVolume := by
      intro m l hl
      simpa [hallPiece, hl] using s.hVolume m ((hallEquiv42 μ tubes n s m).symm ⟨l, hl⟩)
    hNormalization := s.hNormalization, hRadiusScale := s.hRadiusScale }

/-- Relabeling preserves each actual set exactly. -/
theorem hallPiece_at_equiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) :
    hallPiece μ tubes n s m (hallEquiv42 μ tubes n s m p).val = s.retainedPiece m p := by
  classical
  simp [hallPiece]

/-- The chosen representatives retain the compatibility supplied by Hall. -/
theorem hallEquiv42_intersects
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {r : T // r ∈ s.B m} ⊕ {p : K // p ∈ s.P m}) :
    (s.retainedPiece m p ∩ tubes (hallEquiv42 μ tubes n s m p).val).Nonempty :=
  Classical.choose_spec (hallReindexing μ tubes n s m).property p

/-- The one mass sum is unchanged by Hall relabeling. -/
theorem hallPiece_mass_sum
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (∑ l ∈ (hallReindexing μ tubes n s m).val,
      Kakeya.Conditional.mass μ (hallPiece μ tubes n s m l)) =
        ∑ p, Kakeya.Conditional.mass μ (s.retainedPiece m p) := by
  classical
  let e := hallEquiv42 μ tubes n s m
  have h := Equiv.sum_comp e
    (fun l => Kakeya.Conditional.mass μ (hallPiece μ tubes n s m l.val))
  dsimp [e] at h
  simp only [hallPiece_at_equiv] at h
  calc
    _ = ∑ l ∈ (hallReindexing μ tubes n s m).val.attach,
        Kakeya.Conditional.mass μ (hallPiece μ tubes n s m l.val) :=
      (Finset.sum_attach (hallReindexing μ tubes n s m).val
        (fun l => Kakeya.Conditional.mass μ (hallPiece μ tubes n s m l))).symm
    _ = _ := h.symm

/-- Greedy premises stated on the original retained sets, before Hall. -/
structure RetainedGreedyAtLevels
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (s : RetainedDyadicData (K := K) μ tubes n) where
  Q : Kakeya.Eighty4.DyadicIndex (Fintype.card T) → ℕ → Set X
  hScaleLe : ∀ m, Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
    (Fintype.card T : ℝ)
  hUnionMeasurable : ∀ m, MeasurableSet (Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊)
  hUnionSubset : ∀ m, Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      Kakeya.Eighty4.concreteDyadicBand tubes m
  hStep : ∀ m k,
    Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
      (Q m) (k + 1) ≤
      (1 - Kakeya.Eighty4.dyadicScale (Fintype.card T) m / (Fintype.card T : ℝ)) *
        Kakeya.Eighty4.greedyResidual μ (Kakeya.Eighty4.concreteDyadicBand tubes m)
          (Q m) k
  hPieceMeasurable : ∀ m p, MeasurableSet (s.retainedPiece m p)
  hCover : ∀ m, Kakeya.Eighty4.greedyUnion (Q m)
    ⌈(Fintype.card T : ℝ) / Kakeya.Eighty4.dyadicScale (Fintype.card T) m⌉₊ ⊆
      ⋃ p, s.retainedPiece m p

/-- Transport retained measurability and coverage to the constructed family.
The recurrence and greedy union are unchanged. -/
noncomputable def greedy_of_trimmed_hall
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s.toBallLocalizedDyadicData.toRetainedDyadicData)
    (hTubeCount : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((hallReindexing μ tubes n s m).val.card : ℝ) ≤
          4 * (Fintype.card T : ℝ)) :
    GreedyCaptureAtLevels μ tubes n
      (data_of_trimmed_hall μ tubes n s hTubeCount) := by
  classical
  exact {
    Q := c.Q, hScaleLe := c.hScaleLe
    hUnionMeasurable := c.hUnionMeasurable, hUnionSubset := c.hUnionSubset
    hStep := c.hStep
    hPieceMeasurable := by
      intro m l hl
      change MeasurableSet (hallPiece μ tubes n s m l)
      change l ∈ (hallReindexing μ tubes n s m).val at hl
      simpa [hallPiece, hl] using
        c.hPieceMeasurable m ((hallEquiv42 μ tubes n s m).symm ⟨l, hl⟩)
    hCover := by
      intro m x hx
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (c.hCover m hx)
      refine Set.mem_iUnion.mpr ⟨(hallEquiv42 μ tubes n s m p).val, ?_⟩
      refine Set.mem_iUnion.mpr ⟨(hallEquiv42 μ tubes n s m p).property, ?_⟩
      change x ∈ hallPiece μ tubes n s m (hallEquiv42 μ tubes n s m p).val
      rw [hallPiece_at_equiv]
      exact hp }


/-- Hall reindexing, distinct-tube count, greedy capture, and dyadic summation. -/
theorem full_conditional_kakeya_moment_of_trimmed_hall
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s.toBallLocalizedDyadicData.toRetainedDyadicData)
    (hTubeCount : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((hallReindexing μ tubes n s m).val.card : ℝ) ≤
          4 * (Fintype.card T : ℝ))
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
      ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ≤
      (2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * (1 / (1 - Real.exp (-1))) * s.C * s.Z * s.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ) := by
  exact full_conditional_kakeya_moment_of_greedy_cover μ tubes n hn
    (data_of_trimmed_hall μ tubes n s hTubeCount)
    (greedy_of_trimmed_hall μ tubes n s c hTubeCount) hT

/-- Hall reindexing, distinct-tube count, greedy capture, and dyadic summation. -/
theorem full_conditional_kakeya_of_trimmed_hall
    (μ : Measure X) [IsFiniteMeasure μ] (tubes : T → Set X)
    (n : ℕ) (hn : 2 ≤ n)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (c : RetainedGreedyAtLevels μ tubes n s.toBallLocalizedDyadicData.toRetainedDyadicData)
    (hTubeCount : ∀ m,
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((hallReindexing μ tubes n s m).val.card : ℝ) ≤
          4 * (Fintype.card T : ℝ))
    (hT : ∀ i, MeasurableSet (tubes i)) :
    (∫ x, Kakeya.Eighty4.tubeMultiplicity tubes x ^
        ((n : ℝ) / ((n : ℝ) - 1)) ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
      ((2 : ℝ) ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        (4 * (1 / (1 - Real.exp (-1))) * s.C * s.Z * s.radiusCap) *
        ((Nat.log 2 (Fintype.card T) + 1 : ℕ) : ℝ)) ^
          (((n : ℝ) - 1) / (n : ℝ)) := by
  exact full_conditional_kakeya_of_greedy_cover μ tubes n hn
    (data_of_trimmed_hall μ tubes n s hTubeCount)
    (greedy_of_trimmed_hall μ tubes n s c hTubeCount) hT

end Kakeya.Ninety21
