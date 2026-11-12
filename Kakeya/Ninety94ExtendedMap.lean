module
public import Kakeya.Ninety21Bijection
public import Kakeya.Eighty9GreedyGain

/-!
# Ninety94: extension from original tube indices to piece labels

The extension is indexed by ORIGINAL, UNTRIMMED tube indices `l`.
A nonempty localized piece `piece k` is contained in its own trimmed region
`trim k`. The rule for an original tube index `l` and a piece label `k` is

  `piece k ∩ tube l ∩ trim k` is nonempty.

The trimmed region belongs to the TARGET piece; `tube l` remains untrimmed.

A tube-wise uniqueness condition makes this incidence rule the graph of a
partial function. We represent the partial function by `L → Option K`, so
original tubes meeting no retained piece are sent to `none`. This is a total
Lean function without inventing a target for inactive tubes.

Important: greedy gains are disjoint POINTWISE, but this alone is not a proof
that each entire original tube intersects at most one retained piece. That
stronger, tube-wise condition is stated explicitly as `TubeWiseUnique` and
must be discharged using the geometric/selection hypotheses appropriate to
the manuscript. The theorems below prove the extension and the q-fiber bound
once that condition is supplied, without a `sorry` or an extra axiom.
-/

@[expose] public section

namespace Kakeya.Ninety94

attribute [local instance] Classical.propDecidable

variable {L K X T : Type*}

/-- Original untrimmed tubes, nonempty retained pieces, and the trimmed
region in which each target piece lies. -/
structure TubeExtensionData (L K X : Type*) where
  tube : L → Set X
  piece : K → Set X
  trim : K → Set X
  piece_subset_trim : ∀ k, piece k ⊆ trim k
  nonempty_piece : ∀ k, (piece k).Nonempty

/-- Page-14 incidence, with the ORIGINAL tube index in the first argument. -/
def extensionHit (d : TubeExtensionData L K X) (l : L) (k : K) : Prop :=
  (d.piece k ∩ d.tube l ∩ d.trim k).Nonempty

/-- Because `piece k` already lies in its trimmed region, the trim on the
TARGET does not remove any incidence with the UNTRIMMED tube `tube l`. -/
theorem extensionHit_iff_original
    (d : TubeExtensionData L K X) (l : L) (k : K) :
    extensionHit d l k ↔ (d.piece k ∩ d.tube l).Nonempty := by
  constructor
  · rintro ⟨x, ⟨hp, ht⟩, _⟩
    exact ⟨x, hp, ht⟩
  · rintro ⟨x, hp, ht⟩
    exact ⟨x, ⟨hp, ht⟩, d.piece_subset_trim k hp⟩

/-- What is required for the incidence rule to be single-valued on original
tube indices. This is a TUBE-WISE condition, not merely disjointness of gains
at a common point. -/
def TubeWiseUnique (d : TubeExtensionData L K X) : Prop :=
  ∀ (l : L) (k₁ k₂ : K),
    extensionHit d l k₁ → extensionHit d l k₂ → k₁ = k₂

/-- The extended function on original indices. `none` records original
tubes which meet no retained piece. -/
noncomputable def extendedMap (d : TubeExtensionData L K X) (l : L) : Option K :=
  if h : ∃ k : K, extensionHit d l k then
    some (Classical.choose h)
  else none

/-- Under tube-wise uniqueness, the proposed incidence rule is EXACTLY the
graph of the extension. The domain index `l` denotes an original tube. -/
theorem extendedMap_eq_some_iff
    (d : TubeExtensionData L K X) (hUnique : TubeWiseUnique d)
    (l : L) (k : K) :
    extendedMap d l = some k ↔ extensionHit d l k := by
  classical
  by_cases h : ∃ j : K, extensionHit d l j
  · have hc : extensionHit d l (Classical.choose h) := Classical.choose_spec h
    constructor
    · intro heq
      have hk : Classical.choose h = k := by
        have hs : some (Classical.choose h) = some k := by
          simpa [extendedMap, h] using heq
        exact Option.some.inj hs
      simpa [hk] using hc
    · intro hit
      have hk : Classical.choose h = k :=
        hUnique l (Classical.choose h) k hc hit
      simp [extendedMap, h, hk]
  · constructor
    · intro heq
      have hnone : (none : Option K) = some k := by
        simpa [extendedMap, h] using heq
      cases hnone
    · intro hit
      exact False.elim (h ⟨k, hit⟩)

/-- A tube meeting a given retained piece is assigned to that piece. -/
theorem extendedMap_eq_some_of_hit
    (d : TubeExtensionData L K X) (hUnique : TubeWiseUnique d)
    (l : L) (k : K) (h : (d.piece k ∩ d.tube l).Nonempty) :
    extendedMap d l = some k :=
  (extendedMap_eq_some_iff d hUnique l k).2
    ((extensionHit_iff_original d l k).2 h)

/-- Any nonempty retained piece on the dyadic level is intersected by at
least `q` original untrimmed tubes, counted only among `original`. -/
theorem original_degree_ge
    (d : TubeExtensionData L K X)
    (original : Finset L) (q : ℕ)
    (hLevel : ∀ (k : K) (x : X), x ∈ d.piece k →
      q ≤ (original.filter (fun l => x ∈ d.tube l)).card)
    (k : K) :
    q ≤ (original.filter (fun l => extensionHit d l k)).card := by
  classical
  obtain ⟨x, hx⟩ := d.nonempty_piece k
  have hsubset :
      original.filter (fun l => x ∈ d.tube l) ⊆
        original.filter (fun l => extensionHit d l k) := by
    intro l hl
    obtain ⟨hlOriginal, hlTube⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr
      ⟨hlOriginal, (extensionHit_iff_original d l k).2 ⟨x, hx, hlTube⟩⟩
  exact (hLevel k x hx).trans (Finset.card_le_card hsubset)

/-- The q-fold original-tube incidences are q DISTINCT preimages of the
SAME target. The uniqueness hypothesis is what preserves the incidences
when passing from the relation to the function. -/
theorem extendedMap_fiber_ge
    (d : TubeExtensionData L K X) (hUnique : TubeWiseUnique d)
    (original : Finset L) (q : ℕ)
    (hLevel : ∀ (k : K) (x : X), x ∈ d.piece k →
      q ≤ (original.filter (fun l => x ∈ d.tube l)).card)
    (k : K) :
    q ≤ (original.filter (fun l => extendedMap d l = some k)).card := by
  classical
  have hsubset :
      original.filter (fun l => extensionHit d l k) ⊆
        original.filter (fun l => extendedMap d l = some k) := by
    intro l hl
    obtain ⟨hlOriginal, hlHit⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr
      ⟨hlOriginal, (extendedMap_eq_some_iff d hUnique l k).2 hlHit⟩
  exact (original_degree_ge d original q hLevel k).trans
    (Finset.card_le_card hsubset)

/-- The precise double count: each piece has at least `q` original-tube
preimages, while a tube index is assigned by a function to at most one piece.
The set `original` contains no auxiliary tube labels. -/
theorem q_mul_card_le_original [Fintype K]
    (d : TubeExtensionData L K X) (hUnique : TubeWiseUnique d)
    (original : Finset L) (q : ℕ)
    (hLevel : ∀ (k : K) (x : X), x ∈ d.piece k →
      q ≤ (original.filter (fun l => x ∈ d.tube l)).card) :
    q * Fintype.card K ≤ original.card := by
  classical
  let R : K → L → Prop := fun k l => extensionHit d l k
  have hlow : ∀ k ∈ (Finset.univ : Finset K),
      q ≤ (original.bipartiteAbove R k).card := by
    intro k _
    have heq : original.bipartiteAbove R k =
        original.filter (fun l => extensionHit d l k) := by
      ext l
      simp only [Finset.mem_bipartiteAbove, Finset.mem_filter, R]
    rw [heq]
    exact original_degree_ge d original q hLevel k
  have hupp : ∀ l ∈ original,
      ((Finset.univ : Finset K).bipartiteBelow R l).card ≤ 1 := by
    intro l _
    apply Finset.card_le_one.mpr
    intro k hk j hj
    exact hUnique l k j
      ((Finset.mem_bipartiteBelow R).mp hk).2
      ((Finset.mem_bipartiteBelow R).mp hj).2
  have hLower :
      (Finset.univ : Finset K).card * q ≤
        ∑ k ∈ (Finset.univ : Finset K),
          (original.bipartiteAbove R k).card := by
    calc
      (Finset.univ : Finset K).card * q =
          ∑ _k ∈ (Finset.univ : Finset K), q := by
            simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro k hk
        exact hlow k hk)
  have hUpper :
      (∑ l ∈ original,
        ((Finset.univ : Finset K).bipartiteBelow R l).card) ≤
        original.card := by
    calc
      _ ≤ ∑ _l ∈ original, (1 : ℕ) := Finset.sum_le_sum (by
        intro l hl
        exact hupp l hl)
      _ = original.card := by simp
  have hCount :
      (Finset.univ : Finset K).card * q ≤ original.card := by
    calc
      _ ≤ ∑ k ∈ (Finset.univ : Finset K),
          (original.bipartiteAbove R k).card := hLower
      _ = ∑ l ∈ original,
          ((Finset.univ : Finset K).bipartiteBelow R l).card :=
            Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
      _ ≤ original.card := hUpper
  simpa only [Finset.card_univ, Nat.mul_comm] using hCount

/-- Form used after the existing `B ⊕ P ≃ D` reindexing. The target labels
are the subtype of the Hall-enlarged `D`; the domain is the ORIGINAL tube
type `T`, and the resulting numerical bound is `q * |D| ≤ N`.

The existing bijection supplies the labels; the tube-wise uniqueness is a
separate geometric assertion required for THIS extension. -/
theorem q_mul_reindexed_card_le_original [Fintype T]
    (D : Finset T)
    (d : TubeExtensionData T {k : T // k ∈ D} X)
    (hUnique : TubeWiseUnique d) (q : ℕ)
    (hLevel : ∀ (k : {t : T // t ∈ D}) (x : X), x ∈ d.piece k →
      q ≤ ((Finset.univ : Finset T).filter (fun l => x ∈ d.tube l)).card) :
    q * D.card ≤ Fintype.card T := by
  have hbound := q_mul_card_le_original d hUnique
    (Finset.univ : Finset T) q hLevel
  simpa using hbound

/-- Greedy selection as formalized in `Eighty9GreedyGain` gives uniqueness
when TWO gains contain THE SAME POINT. It does not, by itself, assert the
`tube-wise` hypothesis for an untrimmed tube meeting different points. -/
theorem greedy_gain_common_point_unique
    (tube : L → Set X) (F : Set X) (chosen : ℕ → L)
    {i j : ℕ} {x : X}
    (hi : x ∈ Kakeya.Eighty4.concreteGreedyGain tube F chosen i)
    (hj : x ∈ Kakeya.Eighty4.concreteGreedyGain tube F chosen j) :
    i = j := by
  rcases lt_trichotomy i j with hij | heq | hji
  · exact False.elim ((Set.disjoint_left.mp
      (Kakeya.Eighty4.concreteGreedyGain_disjoint tube F chosen hij)) hi hj)
  · exact heq
  · exact False.elim ((Set.disjoint_left.mp
      (Kakeya.Eighty4.concreteGreedyGain_disjoint tube F chosen hji)) hj hi)

end Kakeya.Ninety94
