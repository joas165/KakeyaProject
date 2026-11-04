module
public import Mathlib

/-!
Exact finite membership patterns and disjointness, retained from Covering.lean.
The missing Cordoba diameter localization is not assumed to be proved here.
-/

@[expose] public section

namespace Kakeya
section Partition

variable {X ι : Type*} [Fintype ι] [DecidableEq ι]

/-- J(x): all indices of sets containing x, not just a selected subfamily. -/
noncomputable def membershipPattern (A : ι → Set X) (x : X) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x ∈ A i)

@[simp] theorem mem_membershipPattern (A : ι → Set X) (x : X) (i : ι) :
    i ∈ membershipPattern A x ↔ x ∈ A i := by
  classical
  simp [membershipPattern]

/-- P_J: the points whose FULL membership pattern is exactly J. -/
def exactPiece (A : ι → Set X) (J : Finset ι) : Set X :=
  {x | membershipPattern A x = J}

theorem mem_exactPiece_iff (A : ι → Set X) (J : Finset ι) (x : X) :
    x ∈ exactPiece A J ↔ ∀ i, (x ∈ A i ↔ i ∈ J) := by
  constructor
  · intro hx i
    change membershipPattern A x = J at hx
    rw [← hx]
    exact (mem_membershipPattern A x i).symm
  · intro hx
    change membershipPattern A x = J
    apply Finset.ext
    intro i
    exact (mem_membershipPattern A x i).trans (hx i)

/-- Every point belongs to its own exact piece. -/
theorem mem_exactPiece_own (A : ι → Set X) (x : X) :
    x ∈ exactPiece A (membershipPattern A x) := rfl

/-- Distinct patterns define disjoint pieces, including empty pieces. -/
theorem exactPiece_disjoint (A : ι → Set X) {J K : Finset ι}
    (hJK : J ≠ K) : Disjoint (exactPiece A J) (exactPiece A K) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change membershipPattern A x = J at hx
  change membershipPattern A x = K at hy
  exact hJK (hx.symm.trans hy)

/-- In particular P_J is contained in the full common intersection. -/
theorem exactPiece_subset_common (A : ι → Set X) (J : Finset ι) :
    exactPiece A J ⊆ {x | ∀ i ∈ J, x ∈ A i} := by
  intro x hx i hi
  exact ((mem_exactPiece_iff A J x).mp hx i).mpr hi

/-- Indices absent from the pattern do not contain any point of its piece. -/
theorem exactPiece_excludes (A : ι → Set X) (J : Finset ι)
    {i : ι} (hi : i ∉ J) : exactPiece A J ⊆ (A i)ᶜ := by
  intro x hx hxi
  exact hi (((mem_exactPiece_iff A J x).mp hx i).mp hxi)

/-- A ball bound for the common intersection transfers to its exact piece.
This is just containment; the geometric bound must come from Cordoba's lemma. -/
theorem exactPiece_subset_of_common_subset
    (A : ι → Set X) (J : Finset ι) (B : Set X)
    (hB : {x | ∀ i ∈ J, x ∈ A i} ⊆ B) :
    exactPiece A J ⊆ B :=
  (exactPiece_subset_common A J).trans hB

/-- The admissible patterns at level m, including those with empty pieces. -/
def dyadicPatterns (m : ℕ) : Finset (Finset ι) :=
  Finset.univ.filter (fun J => 2 ^ m ≤ J.card ∧ J.card < 2 ^ (m + 1))

@[simp] theorem mem_dyadicPatterns (m : ℕ) (J : Finset ι) :
    J ∈ dyadicPatterns (ι := ι) m ↔
      2 ^ m ≤ J.card ∧ J.card < 2 ^ (m + 1) := by
  simp [dyadicPatterns]


end Partition
end Kakeya
