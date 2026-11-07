module
public import Kakeya.Eighty9LevelBudget

/-!
# Ninety21: counting over distinct tube indices

Here `D`, `B`, and `extra` are finite sets of tube indices, not tube-ball pairs.
The row bound is proved from disjointness of the trimmed sets. Column coverage
and localized mass capture are separate, explicit hypotheses. No matching or
relabeling theorem is used to infer geometric containment.
-/

@[expose] public section

open scoped BigOperators Classical

namespace Kakeya.Ninety21

variable {T X : Type*} [DecidableEq T]

/-- The page-11 incidence, indexed directly by tubes. -/
def tubeIncidence (tube gain : T → Set X) (l r : T) : Prop :=
  ((tube l ∩ gain l) ∩ (tube r ∩ gain r)).Nonempty

/-- Disjoint trimming forces incident tube indices to agree. -/
theorem eq_of_tubeIncidence
    (tube gain : T → Set X)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    {l r : T} (h : tubeIncidence tube gain l r) : l = r := by
  by_contra hne
  obtain ⟨x, hxl, hxr⟩ := h
  exact (Set.disjoint_left.mp (hDisjoint l r hne)) hxl.2 hxr.2

/-- A nonempty trimmed tube is incident to itself. -/
theorem tubeIncidence_self
    (tube gain : T → Set X) {l : T}
    (h : (tube l ∩ gain l).Nonempty) :
    tubeIncidence tube gain l l := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, hx⟩

/-- The row is counted over `l ∈ D`, with no parent map `l(k)`. -/
theorem tube_row_card_le_one
    (tube gain : T → Set X) (D : Finset T)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    (r : T) :
    (D.filter (fun l => tubeIncidence tube gain l r)).card ≤ 1 := by
  classical
  have hsub : D.filter (fun l => tubeIncidence tube gain l r) ⊆ {r} := by
    intro l hl
    have heq := eq_of_tubeIncidence tube gain hDisjoint (Finset.mem_filter.mp hl).2
    simpa only [Finset.mem_singleton] using heq
  simpa using Finset.card_le_card hsub

/-- Interchanging the two sums preserves exactly the same incidence relation. -/
theorem tube_incidence_sum_swap
    (tube gain : T → Set X) (D B : Finset T) :
    (∑ l ∈ D, ∑ r ∈ B, if tubeIncidence tube gain l r then (1 : ℕ) else 0) =
      ∑ r ∈ B, ∑ l ∈ D, if tubeIncidence tube gain l r then (1 : ℕ) else 0 := by
  classical
  exact Finset.sum_comm

/-- For disjoint trimmed tubes, column coverage implies inclusion of indices.
This proves the count directly without constructing an injection. -/
theorem tube_indices_subset_of_columns
    (tube gain : T → Set X) (D B : Finset T)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    (hColumn : ∀ l ∈ D, ∃ r ∈ B, tubeIncidence tube gain l r) :
    D ⊆ B := by
  intro l hl
  obtain ⟨r, hr, hInc⟩ := hColumn l hl
  have heq := eq_of_tubeIncidence tube gain hDisjoint hInc
  simpa only [heq] using hr

theorem tube_card_le_of_columns
    (tube gain : T → Set X) (D B : Finset T)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    (hColumn : ∀ l ∈ D, ∃ r ∈ B, tubeIncidence tube gain l r) :
    D.card ≤ B.card :=
  Finset.card_le_card (tube_indices_subset_of_columns tube gain D B hDisjoint hColumn)

/-- Column coverage follows by choosing the same tube index, whenever that
index belongs to the selected family and its trimmed tube is nonempty. -/
theorem tube_columns_of_subset
    (tube gain : T → Set X) (D B : Finset T)
    (hsub : D ⊆ B)
    (hNonempty : ∀ l ∈ D, (tube l ∩ gain l).Nonempty) :
    ∀ l ∈ D, ∃ r ∈ B, tubeIncidence tube gain l r := by
  intro l hl
  exact ⟨l, hsub hl, tubeIncidence_self tube gain (hNonempty l hl)⟩

/-- The selected-tube budget passes to the counted tubes. -/
theorem scaled_tube_count
    (tube gain : T → Set X) (D B : Finset T)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    (hColumn : ∀ l ∈ D, ∃ r ∈ B, tubeIncidence tube gain l r)
    (q N A : ℝ) (hq : 0 ≤ q)
    (hBudget : q * (B.card : ℝ) ≤ A * N) :
    q * (D.card : ℝ) ≤ A * N := by
  have hc : (D.card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast tube_card_le_of_columns tube gain D B hDisjoint hColumn
  exact (mul_le_mul_of_nonneg_left hc hq).trans hBudget

/-- Adding at most `ceil (4N/q)` labels gives a budget of `7N`, using
`q * extra.card ≤ 4N + q` and `q ≤ N`. The existence of those labels and
their geometric column coverage are not assumed to follow from this bound. -/
theorem enlarged_selection_budget
    (B extra : Finset T) (q N : ℝ) (hq : 0 ≤ q) (hqN : q ≤ N)
    (hGreedy : q * (B.card : ℝ) ≤ 2 * N)
    (hExtra : q * (extra.card : ℝ) ≤ 4 * N + q) :
    q * ((B ∪ extra).card : ℝ) ≤ 7 * N := by
  have hc : ((B ∪ extra).card : ℝ) ≤ (B.card : ℝ) + (extra.card : ℝ) := by
    exact_mod_cast Finset.card_union_le B extra
  have hm := mul_le_mul_of_nonneg_left hc hq
  nlinarith

/-- Equation (7)'s numerical step, with general counting constant `A`.
The mass capture and per-piece volume bound refer to the SAME tube indices D. -/
theorem localized_level_bound
    (D : Finset T) (mass : T → ℝ) (level H V q N A : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hCapture : level ≤ H * (∑ l ∈ D, mass l))
    (hVolume : ∀ l ∈ D, mass l ≤ V)
    (hCount : q * (D.card : ℝ) ≤ A * N) :
    q * level ≤ A * H * N * V := by
  have hMass := Kakeya.Eighty9.localized_mass_le_card
    D mass level H V hH hCapture hVolume
  calc
    q * level ≤ q * (H * ((D.card : ℝ) * V)) :=
      mul_le_mul_of_nonneg_left hMass hq
    _ = H * ((q * (D.card : ℝ)) * V) := by ring
    _ ≤ H * ((A * N) * V) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCount hV) hH
    _ = A * H * N * V := by ring

/-- Page 11 counting and localized mass combined, conditional on explicit
column coverage, localized mass capture, and the piece-volume bound. -/
theorem localized_level_bound_of_tube_columns
    (tube gain : T → Set X) (D B : Finset T)
    (hDisjoint : ∀ l r, l ≠ r → Disjoint (gain l) (gain r))
    (hColumn : ∀ l ∈ D, ∃ r ∈ B, tubeIncidence tube gain l r)
    (mass : T → ℝ) (level H V q N A : ℝ)
    (hH : 0 ≤ H) (hV : 0 ≤ V) (hq : 0 ≤ q)
    (hBudget : q * (B.card : ℝ) ≤ A * N)
    (hCapture : level ≤ H * (∑ l ∈ D, mass l))
    (hVolume : ∀ l ∈ D, mass l ≤ V) :
    q * level ≤ A * H * N * V := by
  exact localized_level_bound D mass level H V q N A hH hV hq hCapture hVolume
    (scaled_tube_count tube gain D B hDisjoint hColumn q N A hq hBudget)

end Kakeya.Ninety21
