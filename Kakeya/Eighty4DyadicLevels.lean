module
public import Mathlib
public import Kakeya.ConditionalKakeya
public import Kakeya.FinalTubeSum

/-!
# Dyadic levels

Finite dyadic decompositions and scale estimates for tube multiplicity.
-/

@[expose] public section

open MeasureTheory

open scoped BigOperators

namespace Kakeya.Eighty4

def dyadicDepth (N : ℕ) : ℕ := Nat.log 2 N + 1

abbrev DyadicIndex (N : ℕ) : Type := Fin (dyadicDepth N)

theorem dyadicIndex_card (N : ℕ) :
    Fintype.card (DyadicIndex N) = Nat.log 2 N + 1 := by
  exact Fintype.card_fin (Nat.log 2 N + 1)

noncomputable def finiteTubeCount {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : T => x ∈ tubes i)).card

theorem finiteTubeCount_le {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) :
    finiteTubeCount tubes x ≤ Fintype.card T := by
  classical
  unfold finiteTubeCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (by simp)

theorem tubeMultiplicity_eq_count {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) :
    tubeMultiplicity tubes x = (finiteTubeCount tubes x : ℝ) := by
  classical
  calc
    tubeMultiplicity tubes x =
        ∑ i : T, if x ∈ tubes i then (1 : ℝ) else 0 := by
      unfold tubeMultiplicity
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x ∈ tubes i <;> simp [Kakeya.Conditional.chi, hi]
    _ = ∑ i ∈ (Finset.univ.filter (fun i : T => x ∈ tubes i)),
          (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = (finiteTubeCount tubes x : ℝ) := by
      simp [finiteTubeCount]

theorem exists_dyadic_index
    (N k : ℕ) (hk : 0 < k) (hbound : k ≤ N) :
    ∃ m : DyadicIndex N,
      (2 : ℕ) ^ m.val ≤ k ∧ k < (2 : ℕ) ^ (m.val + 1) := by
  let m : ℕ := Nat.log 2 k
  have hmle : m ≤ Nat.log 2 N := Nat.log_mono_right hbound
  have hlo : (2 : ℕ) ^ m ≤ k :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hk)
  have hhi : k < (2 : ℕ) ^ (m + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) k)
  exact ⟨⟨m, by dsimp [dyadicDepth]; omega⟩, hlo, hhi⟩

def dyadicScale (N : ℕ) (m : DyadicIndex N) : ℝ :=
  (2 : ℝ) ^ m.val

def concreteDyadicBand {X T : Type*} [Fintype T]
    (tubes : T → Set X) (m : DyadicIndex (Fintype.card T)) : Set X :=
  {x | dyadicScale (Fintype.card T) m ≤ tubeMultiplicity tubes x ∧
    tubeMultiplicity tubes x < 2 * dyadicScale (Fintype.card T) m}

theorem dyadicScale_pos (N : ℕ) (m : DyadicIndex N) :
    0 < dyadicScale N m := by
  unfold dyadicScale
  positivity

theorem concreteDyadicBand_cover
    {X T : Type*} [Fintype T]
    (tubes : T → Set X) (x : X) :
    tubeMultiplicity tubes x = 0 ∨
      ∃ m : DyadicIndex (Fintype.card T),
        x ∈ concreteDyadicBand tubes m := by
  classical
  let k := finiteTubeCount tubes x
  by_cases hzero : k = 0
  · left
    rw [tubeMultiplicity_eq_count]
    simp [k] at hzero
    simp [hzero]
  · right
    have hk : 0 < k := Nat.pos_of_ne_zero hzero
    obtain ⟨m, hmlo, hmhi⟩ :=
      exists_dyadic_index (Fintype.card T) k hk (finiteTubeCount_le tubes x)
    refine ⟨m, ?_⟩
    change dyadicScale (Fintype.card T) m ≤ tubeMultiplicity tubes x ∧
      tubeMultiplicity tubes x < 2 * dyadicScale (Fintype.card T) m
    rw [tubeMultiplicity_eq_count]
    have hlo : ((2 : ℕ) ^ m.val : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hmlo
    have hhi : (k : ℝ) < ((2 : ℕ) ^ (m.val + 1) : ℝ) := by
      exact_mod_cast hmhi
    constructor
    · simpa [dyadicScale, k] using hlo
    · simpa [dyadicScale, pow_succ, mul_comm, k] using hhi

theorem concreteDyadicBand_upper
    {X T : Type*} [Fintype T]
    (tubes : T → Set X) (m : DyadicIndex (Fintype.card T))
    (x : X) (hx : x ∈ concreteDyadicBand tubes m) :
    tubeMultiplicity tubes x ≤ 2 * dyadicScale (Fintype.card T) m :=
  hx.2.le

theorem concreteDyadicBand_measurable
    {X T : Type*} [MeasurableSpace X] [Fintype T]
    (tubes : T → Set X) (hT : ∀ i, MeasurableSet (tubes i))
    (m : DyadicIndex (Fintype.card T)) :
    MeasurableSet (concreteDyadicBand tubes m) := by
  have hchi : ∀ i : T, Measurable (Kakeya.Conditional.chi (tubes i)) := by
    intro i
    exact measurable_const.indicator (hT i)
  have hf : Measurable (tubeMultiplicity tubes) := by
    unfold tubeMultiplicity
    exact Finset.measurable_sum _ (fun i _ => hchi i)
  change MeasurableSet
    ({x | dyadicScale (Fintype.card T) m ≤ tubeMultiplicity tubes x} ∩
     {x | tubeMultiplicity tubes x < 2 * dyadicScale (Fintype.card T) m})
  exact (measurableSet_Ici.preimage hf).inter
    (measurableSet_Iio.preimage hf)

theorem concreteDyadicBand_condition
    {X T : Type*} [Fintype T] (tubes : T → Set X) :
    ∀ x, tubeMultiplicity tubes x = 0 ∨
      ∃ m : DyadicIndex (Fintype.card T),
        x ∈ concreteDyadicBand tubes m ∧
          tubeMultiplicity tubes x ≤
            2 * dyadicScale (Fintype.card T) m := by
  intro x
  rcases concreteDyadicBand_cover tubes x with hz | ⟨m, hm⟩
  · exact Or.inl hz
  · exact Or.inr ⟨m, hm, concreteDyadicBand_upper tubes m x hm⟩

end Kakeya.Eighty4
