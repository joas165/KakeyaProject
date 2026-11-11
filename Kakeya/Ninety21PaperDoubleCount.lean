module
public import Kakeya.Ninety21ConcreteIntegration

/-!
# The paper's actual regular/exceptional classification, and regular fibers

The family `s.P m` is the existing family of remaining retained trimmed pieces.
There is no separately selected or substituted family.

For p in that family set
  d(p) = #{t : T | (sourcePiece (inr p) ∩ tubes t).Nonempty}.
Theorem 4.6's classification is implemented *definitionally*:
  P_reg = {p in P | 2*d(p) <= N}
  P_exc = {p in P | N < 2*d(p)}.
This is exactly d(p) <= N/2 versus d(p) > N/2 (no real rounding).

The original-tube partial assignment is restricted to P_reg. It contains no
auxiliary labels and makes no row-uniqueness claim about intersections.
The only new incidence/counting assumption is `hFiberLower`, for P_reg alone.
The current Hall image of P_reg is not yet proved to be the distinct
nonintersecting representative image sigma(P_reg) of Theorem 4.6.

This module proves q*|P_reg| <= N, partitions the actual source family, and
obtains q*|D| <= 3*N + q*|P_exc|. It DOES NOT claim the exceptional packing
bound or the final 4N budget. Those require the actual Vitali-ball data,
which `TrimmedHallDyadicData` does not yet encode.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

variable {X T K : Type*} [MeasurableSpace X] [Fintype T]

/-- Number of ORIGINAL tubes meeting an actual remaining retained piece. -/
noncomputable def paperOriginalTubeDegree
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {k : K // k ∈ s.P m}) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r : T =>
    (s.sourcePiece m (Sum.inr p) ∩ tubes r).Nonempty)).card

/-- The paper's `P_m^reg`: precisely the actual pieces with d(P) ≤ N/2. -/
noncomputable def paperRegularPieces
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Finset {k : K // k ∈ s.P m} := by
  classical
  exact Finset.univ.filter (fun p =>
    2 * paperOriginalTubeDegree μ tubes n s m p ≤ Fintype.card T)

/-- The paper's `P_m^exc`: precisely the actual pieces with d(P) > N/2. -/
noncomputable def paperExceptionalPieces
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Finset {k : K // k ∈ s.P m} := by
  classical
  exact Finset.univ.filter (fun p =>
    Fintype.card T < 2 * paperOriginalTubeDegree μ tubes n s m p)

theorem mem_paperRegularPieces
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {k : K // k ∈ s.P m}) :
    p ∈ paperRegularPieces μ tubes n s m ↔
      2 * paperOriginalTubeDegree μ tubes n s m p ≤ Fintype.card T := by
  classical
  simp [paperRegularPieces]

theorem mem_paperExceptionalPieces
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {k : K // k ∈ s.P m}) :
    p ∈ paperExceptionalPieces μ tubes n s m ↔
      Fintype.card T < 2 * paperOriginalTubeDegree μ tubes n s m p := by
  classical
  simp [paperExceptionalPieces]

/-- Every actual retained piece is in exactly one of the two classes. -/
theorem paper_regular_exceptional_partition
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Disjoint (paperRegularPieces μ tubes n s m)
        (paperExceptionalPieces μ tubes n s m) ∧
      paperRegularPieces μ tubes n s m ∪
        paperExceptionalPieces μ tubes n s m = Finset.univ := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp he
    have hr := (mem_paperRegularPieces μ tubes n s m p).mp hp
    have hx := (mem_paperExceptionalPieces μ tubes n s m p).mp he
    omega
  · ext p
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : 2 * paperOriginalTubeDegree μ tubes n s m p ≤ Fintype.card T
    · exact Or.inl ((mem_paperRegularPieces μ tubes n s m p).mpr h)
    · have hx : Fintype.card T < 2 * paperOriginalTubeDegree μ tubes n s m p := by
        omega
      exact Or.inr ((mem_paperExceptionalPieces μ tubes n s m p).mpr hx)

/-- In particular, the split does not create or discard any retained pieces. -/
theorem paper_regular_exceptional_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (paperRegularPieces μ tubes n s m).card +
      (paperExceptionalPieces μ tubes n s m).card = (s.P m).card := by
  classical
  obtain ⟨hdisj, hcover⟩ := paper_regular_exceptional_partition μ tubes n s m
  calc
    (paperRegularPieces μ tubes n s m).card +
        (paperExceptionalPieces μ tubes n s m).card =
        (paperRegularPieces μ tubes n s m ∪
          paperExceptionalPieces μ tubes n s m).card :=
          (Finset.card_union_of_disjoint hdisj).symm
    _ = (s.P m).card := by rw [hcover]; simp

/-- Each exceptional piece keeps its actual selected trimmed-tube parent.
No new parent function or piece family is introduced by classification. -/
theorem paperExceptional_parent_selected
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {p : {k : K // k ∈ s.P m} //
      p ∈ paperExceptionalPieces μ tubes n s m}) :
    s.parent m p.val ∈ s.B m := s.hParent m p.val

/-- The exceptional pieces are still the same localized trimmed subsets. -/
theorem paperExceptional_trimmed
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {p : {k : K // k ∈ s.P m} //
      p ∈ paperExceptionalPieces μ tubes n s m}) :
    s.sourcePiece m (Sum.inr p.val) ⊆
      tubes (s.parent m p.val) ∩ s.gain m (s.parent m p.val) :=
  s.hTrimmed m p.val

/-- The Hall index assigned to a regular *actual retained piece*. This is
only a relabeling of that piece, not a new piece or original-tube incidence. -/
noncomputable def paperRegularIndex
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (p : {p : {k : K // k ∈ s.P m} //
      p ∈ paperRegularPieces μ tubes n s m}) : T :=
  (hallEquiv42 μ tubes n s m (Sum.inr p.val)).val

/-- Regular pieces have distinct representatives because Hall is a bijection. -/
theorem paperRegularIndex_injective
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    Function.Injective (paperRegularIndex μ tubes n s m) := by
  intro p p' h
  have he : hallEquiv42 μ tubes n s m (Sum.inr p.val) =
      hallEquiv42 μ tubes n s m (Sum.inr p'.val) := Subtype.ext h
  have hp : p.val = p'.val :=
    Sum.inr.inj ((hallEquiv42 μ tubes n s m).injective he)
  exact Subtype.ext hp

/-- The finite set of Hall labels of regular actual pieces. This is the
image under the *existing* Hall equivalence, not a claim that its values are
the nonintersecting representatives of Theorem 4.6. -/
noncomputable def paperRegularIndices
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) : Finset T := by
  classical
  exact Finset.univ.image (paperRegularIndex μ tubes n s m)

/-- The regular labels really lie in the existing Hall reindexing `D_m`. -/
theorem paperRegularIndices_subset_hall
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    paperRegularIndices μ tubes n s m ⊆
      (hallReindexing μ tubes n s m).val := by
  classical
  intro r hr
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hr
  exact (hallEquiv42 μ tubes n s m (Sum.inr p.val)).property

/-- The regular source labels and their distinct Hall indices are equivalent.
This is the regular image under the currently implemented intersection-compatible
Hall reindexing. The paper's nonintersecting sigma from Theorem 4.6 is a
separate construction and is NOT identified with this map here. -/
noncomputable def paperRegularIndexEquiv
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    {p : {k : K // k ∈ s.P m} //
      p ∈ paperRegularPieces μ tubes n s m} ≃
      {r : T // r ∈ paperRegularIndices μ tubes n s m} := by
  classical
  let f : {p : {k : K // k ∈ s.P m} //
      p ∈ paperRegularPieces μ tubes n s m} →
      {r : T // r ∈ paperRegularIndices μ tubes n s m} :=
    fun p => ⟨paperRegularIndex μ tubes n s m p,
      Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p p' h
    have hval : (f p).val = (f p').val :=
      congrArg Subtype.val h
    change paperRegularIndex μ tubes n s m p =
      paperRegularIndex μ tubes n s m p' at hval
    exact paperRegularIndex_injective μ tubes n s m hval
  · intro r
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp r.property
    refine ⟨p, ?_⟩
    apply Subtype.ext
    exact hp

/-- The sigma image has exactly as many indices as geometric regular pieces. -/
theorem paperRegularIndices_card
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T)) :
    (paperRegularIndices μ tubes n s m).card =
      (paperRegularPieces μ tubes n s m).card := by
  classical
  have hc := Fintype.card_congr (paperRegularIndexEquiv μ tubes n s m)
  simpa only [Fintype.card_coe] using hc.symm

/-- A PARTIAL assignment from ORIGINAL tubes to sigma(P_m^reg) only.
It is single-valued by its type; it does not assert that an original tube
intersects only one geometrical piece. Auxiliary tubes are not in its domain.
This is conditional on lower fibers for the indices it actually uses. -/
noncomputable def paperOriginalTubeMapReg
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (t : T) : Option {r : T //
      r ∈ paperRegularIndices μ tubes n s m} := by
  classical
  exact if h : ∃ p : {p : {k : K // k ∈ s.P m} //
      p ∈ paperRegularPieces μ tubes n s m},
      (s.sourcePiece m (Sum.inr p.val) ∩ tubes t).Nonempty
    then some (paperRegularIndexEquiv μ tubes n s m (Classical.choose h))
    else none

/-- A fiber count needs single-valuedness, NOT uniqueness of tube-piece
intersections. It can be applied only with valid geometric lower fibers. -/
theorem paper_double_count_fibers
    {S R : Type*} [Fintype S] [Fintype R] [DecidableEq S]
    (f : R → Option S) (q : ℝ)
    (hFiberLower : ∀ p : S,
      q ≤ ∑ r : R, if f r = some p then (1 : ℝ) else 0) :
    q * (Fintype.card S : ℝ) ≤ (Fintype.card R : ℝ) := by
  classical
  calc
    q * (Fintype.card S : ℝ) = ∑ p : S, q := by simp [mul_comm]
    _ ≤ ∑ p : S, ∑ r : R,
        if f r = some p then (1 : ℝ) else 0 := by
          exact Finset.sum_le_sum (by intro p hp; exact hFiberLower p)
    _ = ∑ r : R, ∑ p : S,
        if f r = some p then (1 : ℝ) else 0 := by
          rw [Finset.sum_comm]
    _ ≤ ∑ r : R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      cases h : f r with
      | none => simp
      | some p => simp
    _ = (Fintype.card R : ℝ) := by simp

/-- The SOLE additional incidence assumption, *only* for regular pieces and
*only* over ORIGINAL tubes. The classification is no longer an input. -/
theorem paper_regular_count_of_fibers
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hFiberLower : ∀ r : {r : T //
      r ∈ paperRegularIndices μ tubes n s m},
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paperOriginalTubeMapReg μ tubes n s m ell = some r
          then (1 : ℝ) else 0) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      ((paperRegularPieces μ tubes n s m).card : ℝ) ≤
        (Fintype.card T : ℝ) := by
  classical
  have hf := paper_double_count_fibers
    (paperOriginalTubeMapReg μ tubes n s m)
    (Kakeya.Eighty4.dyadicScale (Fintype.card T) m)
    hFiberLower
  simpa only [Fintype.card_coe, paperRegularIndices_card] using hf

/-- The paper double count, now over the *defined geometric* regular pieces.
The exceptional count is an explicit remainder, not an assumption. -/
theorem paper_hall_count_with_exceptional_remainder
    (μ : Measure X) (tubes : T → Set X) (n : ℕ)
    (s : TrimmedHallDyadicData (K := K) μ tubes n)
    (m : Kakeya.Eighty4.DyadicIndex (Fintype.card T))
    (hFiberLower : ∀ r : {r : T //
      r ∈ paperRegularIndices μ tubes n s m},
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m ≤
        ∑ ell : T,
          if paperOriginalTubeMapReg μ tubes n s m ell = some r
          then (1 : ℝ) else 0) :
    Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
      (((hallReindexing μ tubes n s m).val.card : ℝ)) ≤
        3 * (Fintype.card T : ℝ) +
          Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
            ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
  classical
  let q := Kakeya.Eighty4.dyadicScale (Fintype.card T) m
  have hReg := paper_regular_count_of_fibers μ tubes n s m hFiberLower
  have hGreedy := s.hGreedy m
  have hPart : ((s.P m).card : ℝ) =
      ((paperRegularPieces μ tubes n s m).card : ℝ) +
      ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
    exact_mod_cast (paper_regular_exceptional_card μ tubes n s m).symm
  have hHall : ((hallReindexing μ tubes n s m).val.card : ℝ) =
      ((s.B m).card : ℝ) + ((s.P m).card : ℝ) := by
    exact_mod_cast hall_reindexed_card μ tubes n s m
  change q * ((hallReindexing μ tubes n s m).val.card : ℝ) ≤
    3 * (Fintype.card T : ℝ) +
      q * ((paperExceptionalPieces μ tubes n s m).card : ℝ)
  calc
    q * ((hallReindexing μ tubes n s m).val.card : ℝ) =
        q * ((s.B m).card : ℝ) + q * ((s.P m).card : ℝ) := by rw [hHall]; ring
    _ = q * ((s.B m).card : ℝ) +
        q * ((paperRegularPieces μ tubes n s m).card : ℝ) +
          q * ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
            rw [hPart]; ring
    _ ≤ 3 * (Fintype.card T : ℝ) +
        q * ((paperExceptionalPieces μ tubes n s m).card : ℝ) := by
          have hReg' : q * ((paperRegularPieces μ tubes n s m).card : ℝ) ≤
              (Fintype.card T : ℝ) := hReg
          have hGreedy' : q * ((s.B m).card : ℝ) ≤
              2 * (Fintype.card T : ℝ) := hGreedy
          nlinarith

end Kakeya.Ninety21
