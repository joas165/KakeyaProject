module
public import Mathlib

/-!
Minimal geometric definitions retained from the larger Kakeya Geometry.lean.
The Cordoba cap-net/diameter arguments are NOT silently treated as established.
-/

@[expose] public section

namespace Kakeya

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Length-one tube centered at p, with transverse radius delta. -/
def unitTube {n : ℕ} (p v : Space n) (δ : ℝ) : Set (Space n) :=
  {x | ∃ (t : ℝ) (w : Space n),
    |t| ≤ (1 : ℝ) / 2 ∧
    inner ℝ w v = 0 ∧
    ‖w‖ ≤ δ ∧
    x = p + t • v + w}

end Kakeya
