module
public import Mathlib

/-!
# Reindexed tube-wise Vitali labels

Finite indexing equivalences for Vitali pieces selected within tube fibers.
-/

@[expose] public section

namespace Kakeya.Eighty9

section TubeWiseReindex

variable {T I K X : Type*} [MetricSpace X]

def TubeWiseVitaliLabel (B : Finset T) (S : T → Finset I) :=
  Σ j : {j : T // j ∈ B}, {i : I // i ∈ S j.val}

noncomputable instance tubeWiseVitaliLabelFintype
    (B : Finset T) (S : T → Finset I) : Fintype (TubeWiseVitaliLabel B S) := by
  classical
  unfold TubeWiseVitaliLabel
  infer_instance

end TubeWiseReindex

end Kakeya.Eighty9
