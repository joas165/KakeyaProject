module
public import Kakeya.Ninety21Bijection
public import Kakeya.Ninety21TubeIndexCounting
public import Kakeya.SelectionComparison

/-!
# Ninety21: bridge from the Hall bijection to tube-indexed level counting

The Hall bijection has domain `B ⊕ P` and codomain the enlarged set of
*distinct tube indices* `D`. Hence `|D| = |B| + |P|`. In particular,
`q * |D| ≲ N` follows from the selected-incidence double-count theorem,
which derives `q * |P| ≤ 2N` from coverage and row uniqueness for one
consistent relation `R`. No independent scale-sensitive piece-budget
hypothesis is required in the concrete Hall-bijection corollary.

The mass transported to a new label is the mass of the ORIGINAL localized
piece, not the mass of an intersection with its newly assigned tube. In fact,
`localized_nonintersecting_bijection` assigns that label to a disjoint tube.
This file never infers a geometric containment from the Hall assignment.

The original column-counting theorem in `Ninety21TubeIndexCounting` is left
unchanged. Its hypotheses force `D ⊆ B`, and thus it is a different case
from the enlarged `B ⊆ D` constructed by Hall matching here.
-/

@[expose] public section

open scoped BigOperators Classical

namespace Kakeya.Ninety21

variable {P T : Type*} [Fintype P]

/-- A cardinality identity for a bijective reindexing gives the required
`q`-scaled tube budget, provided the remaining pieces have their own
`q`-scaled cardinality bound. -/
theorem scaled_count_from_bijection
    (B D : Finset T) (q N C : ℝ)
    (hCard : D.card = B.card + Fintype.card P)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hPieces : q * (Fintype.card P : ℝ) ≤ C * N) :
    q * (D.card : ℝ) ≤ (2 + C) * N := by
  have hCard' : (D.card : ℝ) = (B.card : ℝ) + (Fintype.card P : ℝ) := by
    exact_mod_cast hCard
  calc
    q * (D.card : ℝ) =
        q * (B.card : ℝ) + q * (Fintype.card P : ℝ) := by
          rw [hCard']
          ring
    _ ≤ 2 * N + C * N := add_le_add hGreedy hPieces
    _ = (2 + C) * N := by ring

/-- The piece budget follows by double counting the SAME incidence relation
in the column and row directions. The column and row assumptions are
explicit: no extra numerical hypothesis `q * |P| ≤ 2N` is needed. -/
private theorem selected_piece_budget_from_double_count [Fintype T]
    (R : T → P → Prop) (B : Finset T) (q N : ℝ)
    (hq : 0 ≤ q)
    (hColumn : ∀ p : P, ∃ j ∈ B, R j p)
    (hRow : ∀ j ∈ B,
      Kakeya.Seventy7.weight R (fun _ => 1) j ≤ 1)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N) :
    q * (Fintype.card P : ℝ) ≤ 2 * N := by
  classical
  have hCard : (Fintype.card P : ℝ) ≤ (B.card : ℝ) := by
    calc
      (Fintype.card P : ℝ) = ∑ _p : P, (1 : ℝ) := by simp
      _ ≤ ∑ p : P, Kakeya.Seventy7.degree R B p :=
        Finset.sum_le_sum (fun p _ =>
          Kakeya.Seventy7.degree_ge_one_of_covered R B p (hColumn p))
      _ = ∑ j ∈ B, Kakeya.Seventy7.weight R (fun _ => 1) j :=
        Kakeya.Seventy7.incidence_double_count R B
      _ ≤ ∑ _j ∈ B, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => hRow j hj)
      _ = (B.card : ℝ) := by simp
  exact (mul_le_mul_of_nonneg_left hCard hq).trans hGreedy

/-- The existing selected-incidence double count supplies the scale-sensitive
piece budget for the *same* relation `R` in the column and row conditions.
Here `D` is the enlarged family of distinct Hall labels, so the bound is
`q * |D| ≤ 4N`, not the `D ⊆ B` conclusion of the older row-count lemma. -/
theorem scaled_count_from_selected_incidence [Fintype T]
    (R : T → P → Prop) (B D : Finset T) (q N : ℝ)
    (hq : 0 ≤ q)
    (hCard : D.card = B.card + Fintype.card P)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hColumn : ∀ p : P, ∃ j ∈ B, R j p)
    (hRow : ∀ j ∈ B,
      Kakeya.Seventy7.weight R (fun _ => 1) j ≤ 1) :
    q * (D.card : ℝ) ≤ 4 * N := by
  have hPieces : q * (Fintype.card P : ℝ) ≤ 2 * N :=
    selected_piece_budget_from_double_count
      R B q N hq hColumn hRow hGreedy
  have hCount :=
    scaled_count_from_bijection (P := P) B D q N 2
      hCard hGreedy hPieces
  convert hCount using 1; ring

/-- Hall matching combined with the existing double-count theorem.
The piece budget is derived from selected-incidence column coverage and
row uniqueness for `R`, not postulated as a separate numerical hypothesis.
The matching relation `hit` remains independent: a Hall label need not be
an original tube that intersects (or contains) its transported piece. -/
theorem exists_scaled_bijection_of_greedy [Fintype T]
    (hit : P → T → Prop) (R : T → P → Prop)
    (B : Finset T) (q : ℕ)
    (hq : 8 ≤ q)
    (hGreedy : q * B.card ≤ 2 * Fintype.card T)
    (hP : 4 * Fintype.card P ≤ Fintype.card T)
    (hDegree : ∀ p, 2 * (Finset.univ.filter (hit p)).card ≤ Fintype.card T)
    (hColumn : ∀ p : P, ∃ j ∈ B, R j p)
    (hRow : ∀ j ∈ B,
      Kakeya.Seventy7.weight R (fun _ => 1) j ≤ 1) :
    ∃ (D : Finset T) (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D}),
      B ⊆ D ∧
      (∀ r, (e (Sum.inl r)).val = r.val) ∧
      (∀ p, (e (Sum.inr p)).val ∉ B ∧ ¬ hit p (e (Sum.inr p)).val) ∧
      D.card = B.card + Fintype.card P ∧
      (q : ℝ) * (D.card : ℝ) ≤ 4 * (Fintype.card T : ℝ) := by
  obtain ⟨D, e, hBD, hfix, hgood, hcard⟩ :=
    nonintersecting_bijection_of_greedy hit B q hq hGreedy hP hDegree
  have hGreedyReal :
      (q : ℝ) * (B.card : ℝ) ≤ 2 * (Fintype.card T : ℝ) := by
    exact_mod_cast hGreedy
  refine ⟨D, e, hBD, hfix, hgood, hcard, ?_⟩
  exact scaled_count_from_selected_incidence (P := P)
    R B D (q : ℝ) (Fintype.card T : ℝ)
    (by positivity) hcard hGreedyReal hColumn hRow

/-- Transport the mass of each ORIGINAL selected object or localized piece
to its distinct label in `D`. The label assigned to a piece is not asserted
to be the index of a tube containing that piece. -/
noncomputable def transportedMass
    (B D : Finset T)
    (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D})
    (selectedMass : {r : T // r ∈ B} → ℝ) (pieceMass : P → ℝ)
    (l : T) : ℝ :=
  if h : l ∈ D then
    Sum.elim selectedMass pieceMass (e.symm ⟨l, h⟩)
  else 0

/-- Reindexing along the bijection preserves the total localized mass,
while the final sum is indexed directly over the **tube labels** `l ∈ D`. -/
theorem transported_mass_sum
    (B D : Finset T)
    (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D})
    (selectedMass : {r : T // r ∈ B} → ℝ) (pieceMass : P → ℝ) :
    (∑ l ∈ D, transportedMass B D e selectedMass pieceMass l) =
      (∑ r : {r : T // r ∈ B}, selectedMass r) +
        (∑ p : P, pieceMass p) := by
  classical
  have heq :
      (∑ s : ({r : T // r ∈ B} ⊕ P),
        Sum.elim selectedMass pieceMass s) =
        (∑ l : {r : T // r ∈ D},
          Sum.elim selectedMass pieceMass (e.symm l)) := by
    simpa using (Equiv.sum_comp e
      (fun l : {r : T // r ∈ D} =>
        Sum.elim selectedMass pieceMass (e.symm l)))
  calc
    (∑ l ∈ D, transportedMass B D e selectedMass pieceMass l) =
        (∑ l ∈ D.attach, transportedMass B D e selectedMass pieceMass l.val) :=
          (Finset.sum_attach D (transportedMass B D e selectedMass pieceMass)).symm
    _ = (∑ l : {r : T // r ∈ D},
          Sum.elim selectedMass pieceMass (e.symm l)) := by
            simp [transportedMass]
    _ = (∑ s : ({r : T // r ∈ B} ⊕ P),
          Sum.elim selectedMass pieceMass s) := heq.symm
    _ = (∑ r : {r : T // r ∈ B}, selectedMass r) +
          (∑ p : P, pieceMass p) := by
            simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Equation (7) for an enlarged set of distinct tube labels coming from
Hall matching. Volume and capture bounds apply to the ORIGINAL masses,
transported to `D`; they are not inferred from nonintersecting tube labels. -/
theorem localized_level_bound_of_bijection
    (B D : Finset T)
    (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D})
    (selectedMass : {r : T // r ∈ B} → ℝ) (pieceMass : P → ℝ)
    (level H V q N C : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hCard : D.card = B.card + Fintype.card P)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hPieces : q * (Fintype.card P : ℝ) ≤ C * N)
    (hCapture : level ≤ H * ((∑ r : {r : T // r ∈ B}, selectedMass r) +
      (∑ p : P, pieceMass p)))
    (hSelectedVolume : ∀ r, selectedMass r ≤ V)
    (hPieceVolume : ∀ p, pieceMass p ≤ V) :
    q * level ≤ (2 + C) * H * N * V := by
  let mass := transportedMass B D e selectedMass pieceMass
  have hTransport :
      (∑ l ∈ D, mass l) =
        (∑ r : {r : T // r ∈ B}, selectedMass r) +
        (∑ p : P, pieceMass p) :=
    transported_mass_sum B D e selectedMass pieceMass
  have hCapture' : level ≤ H * (∑ l ∈ D, mass l) := by
    rw [hTransport]
    exact hCapture
  have hVolume' : ∀ l ∈ D, mass l ≤ V := by
    intro l hl
    change transportedMass B D e selectedMass pieceMass l ≤ V
    have hMass :
        transportedMass B D e selectedMass pieceMass l =
          Sum.elim selectedMass pieceMass (e.symm ⟨l, hl⟩) := by
      simp [transportedMass, hl]
    rw [hMass]
    cases hrep : e.symm ⟨l, hl⟩ with
    | inl r => simpa only [hrep, Sum.elim_inl] using hSelectedVolume r
    | inr p => simpa only [hrep, Sum.elim_inr] using hPieceVolume p
  have hCount : q * (D.card : ℝ) ≤ (2 + C) * N :=
    scaled_count_from_bijection (P := P) B D q N C hCard hGreedy hPieces
  exact localized_level_bound D mass level H V q N (2 + C)
    hH hV hq hCapture' hVolume' hCount

/-- The concrete localized level estimate uses the selected-incidence
DOUBLE COUNT to discharge the piece budget. It preserves the sum of
original localized masses under the Hall reindexing; the Hall-assigned
label is never treated as a geometrically containing tube. -/
theorem localized_level_bound_of_double_counted_bijection [Fintype T]
    (R : T → P → Prop) (B D : Finset T)
    (e : ({r : T // r ∈ B} ⊕ P) ≃ {r : T // r ∈ D})
    (selectedMass : {r : T // r ∈ B} → ℝ) (pieceMass : P → ℝ)
    (level H V q N : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hCard : D.card = B.card + Fintype.card P)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hColumn : ∀ p : P, ∃ j ∈ B, R j p)
    (hRow : ∀ j ∈ B,
      Kakeya.Seventy7.weight R (fun _ => 1) j ≤ 1)
    (hCapture : level ≤ H * ((∑ r : {r : T // r ∈ B}, selectedMass r) +
      (∑ p : P, pieceMass p)))
    (hSelectedVolume : ∀ r, selectedMass r ≤ V)
    (hPieceVolume : ∀ p, pieceMass p ≤ V) :
    q * level ≤ 4 * H * N * V := by
  have hPieces : q * (Fintype.card P : ℝ) ≤ 2 * N :=
    selected_piece_budget_from_double_count
      R B q N hq hColumn hRow hGreedy
  have hBound := localized_level_bound_of_bijection
    B D e selectedMass pieceMass level H V q N 2
    hH hV hq hCard hGreedy hPieces
    hCapture hSelectedVolume hPieceVolume
  convert hBound using 1; ring

end Kakeya.Ninety21
