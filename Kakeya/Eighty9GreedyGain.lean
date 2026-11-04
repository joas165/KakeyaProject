module
public import Mathlib

/-!
Only the greedy gain definition and proofs of subset, measurability,
and pairwise disjointness, extracted from Eighty4ConcreteGeometry.lean.
-/

@[expose] public section

namespace Kakeya.Eighty4
/-- The points newly gained by the kth greedy-selected original tube. -/
def concreteGreedyGain {X T : Type*}
    (tubes : T → Set X) (F : Set X) (chosen : ℕ → T) (k : ℕ) :
    Set X :=
  (F ∩ tubes (chosen k)) \ (⋃ i ∈ Finset.range k, tubes (chosen i))

theorem concreteGreedyGain_subset_level {X T : Type*}
    (tubes : T → Set X) (F : Set X) (chosen : ℕ → T) (k : ℕ) :
    concreteGreedyGain tubes F chosen k ⊆ F := by
  intro x hx
  exact hx.1.1

theorem concreteGreedyGain_subset_tube {X T : Type*}
    (tubes : T → Set X) (F : Set X) (chosen : ℕ → T) (k : ℕ) :
    concreteGreedyGain tubes F chosen k ⊆ tubes (chosen k) := by
  intro x hx
  exact hx.1.2

theorem concreteGreedyGain_measurable
    {X T : Type*} [MeasurableSpace X]
    (tubes : T → Set X) (F : Set X) (chosen : ℕ → T)
    (hF : MeasurableSet F)
    (hT : ∀ i, MeasurableSet (tubes i)) (k : ℕ) :
    MeasurableSet (concreteGreedyGain tubes F chosen k) := by
  unfold concreteGreedyGain
  apply (hF.inter (hT (chosen k))).diff
  exact MeasurableSet.iUnion (fun i =>
    MeasurableSet.iUnion (fun _ => hT (chosen i)))

/-- Different greedy gains do not overlap, independently of the underlying
    overlap of the original tube family. -/
theorem concreteGreedyGain_disjoint
    {X T : Type*} (tubes : T → Set X) (F : Set X)
    (chosen : ℕ → T) {i j : ℕ} (hij : i < j) :
    Disjoint (concreteGreedyGain tubes F chosen i)
      (concreteGreedyGain tubes F chosen j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hxEarlier : x ∈ ⋃ r ∈ Finset.range j, tubes (chosen r) := by
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hij, (concreteGreedyGain_subset_tube tubes F chosen i) hxi⟩⟩
  exact hxj.2 hxEarlier


end Kakeya.Eighty4
