module

public import Kakeya.Ninety21EuclideanFiniteNet

/-!
# Angular-cap counting for separated directions

A finite net controls the number of separated directions in an angular cap.
The nontransverse set supplies the near-direction indices used in exceptional
parent-ball counting.
-/

@[expose] public section

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- Separated points admit at most one representative in each open
half-separation net ball. -/
theorem separated_finset_card_le_net_card
    {X I : Type*} [MetricSpace X]
    (points : I → X) (J : Finset I) (Z : Finset X)
    (ε : ℝ) (hε : 0 < ε)
    (hSeparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ε ≤ dist (points i) (points j))
    (hNet : ∀ i ∈ J, ∃ z ∈ Z, dist (points i) z < ε / 2) :
    J.card ≤ Z.card := by
  classical
  let pick : {i : I // i ∈ J} → {z : X // z ∈ Z} :=
    fun i => ⟨Classical.choose (hNet i.val i.property),
      (Classical.choose_spec (hNet i.val i.property)).1⟩
  have hpick : Function.Injective pick := by
    intro i j heq
    apply Subtype.ext
    by_contra hij
    have hz : (pick i).val = (pick j).val := congrArg Subtype.val heq
    have hiClose : dist (points i.val) (pick i).val < ε / 2 :=
      (Classical.choose_spec (hNet i.val i.property)).2
    have hjClose : dist (points j.val) (pick j).val < ε / 2 :=
      (Classical.choose_spec (hNet j.val j.property)).2
    have hjClose' : dist (pick i).val (points j.val) < ε / 2 := by
      rw [hz, dist_comm]
      exact hjClose
    have ht := dist_triangle (points i.val) (pick i).val (points j.val)
    have hsep := hSeparated i.val i.property j.val j.property hij
    linarith
  have hc := Fintype.card_le_of_injective pick hpick
  simpa only [Fintype.card_coe] using hc

/-- Original tube indices whose directions fail the quantitative
transversality inequality with a given parent direction. -/
noncomputable def nonTransverseDirectionIndices
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n) (θ : ℝ) (r : T) : Finset T :=
  Finset.univ.filter (fun ell =>
    ¬ TransverseDirections (direction r) (direction ell) θ)

/-- Original tube directions outside the angular cap are transverse. -/
theorem transverse_of_not_mem_nonTransverseDirectionIndices
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n) (θ : ℝ) (r ell : T)
    (h : ell ∉ nonTransverseDirectionIndices direction θ r) :
    TransverseDirections (direction r) (direction ell) θ := by
  classical
  by_contra hnot
  apply h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩

/-- A half-separation net of a near-direction family, together with a
lower bound on the total number of directions, gives the angular-cap budget. -/
theorem nonTransverseDirectionIndices_card_budget_of_net
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n) (ε θ : ℝ) (A : ℕ)
    (hε : 0 < ε)
    (hSeparated : ∀ r ell : T, r ≠ ell →
      ε ≤ dist (direction r) (direction ell))
    (hCapNet : ∀ r : T, ∃ Z : Finset (Kakeya.Space n),
      Z.card ≤ A ∧
      ∀ ell ∈ nonTransverseDirectionIndices direction θ r,
        ∃ z ∈ Z, dist (direction ell) z < ε / 2)
    (hPopulation : 4 * A ≤ Fintype.card T) :
    ∀ r : T, 4 * (nonTransverseDirectionIndices direction θ r).card ≤
      Fintype.card T := by
  classical
  intro r
  obtain ⟨Z, hZ, hNet⟩ := hCapNet r
  have hSep : ∀ i ∈ nonTransverseDirectionIndices direction θ r,
      ∀ j ∈ nonTransverseDirectionIndices direction θ r,
      i ≠ j → ε ≤ dist (direction i) (direction j) := by
    intro i _ j _ hij
    exact hSeparated i j hij
  have hCard := separated_finset_card_le_net_card
    direction (nonTransverseDirectionIndices direction θ r) Z
    ε hε hSep hNet
  omega

/-- Exceptional-piece budget for separated directions with a uniformly
bounded near-direction net. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_angular_cap_net
    {n : ℕ} {T : Type*} [Fintype T]
    (μ : MeasureTheory.Measure (Kakeya.Space n))
    (center direction : T → Kakeya.Space n)
    (δ θ ε : ℝ) (A : ℕ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n d.retained)
    (hθ : 0 < θ) (hε : 0 < ε)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hSeparated : ∀ r ell : T, r ≠ ell →
      ε ≤ dist (direction r) (direction ell))
    (hCapNet : ∀ r : T, ∃ Z : Finset (Kakeya.Space n),
      Z.card ≤ A ∧
      ∀ ell ∈ nonTransverseDirectionIndices direction θ r,
        ∃ z ∈ Z, dist (direction ell) z < ε / 2)
    (hPopulation : 4 * A ≤ Fintype.card T)
    (hParentSelected : ∀ m r,
      r ∈ (d.retained.toBallLocalized μ n b).B m → r ∈ g.B m) :
    ∃ L : ℕ, ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
      δ ≤ d.radius m →
      Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
        ((paperExceptionalPieces μ
          (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n
          (d.retained.toBallLocalized μ n b).toRetainedDyadicData m).card : ℝ) ≤
        8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  have hNear := nonTransverseDirectionIndices_card_budget_of_net
    direction ε θ A hε hSeparated hCapNet hPopulation
  exact d.exceptional_scaled_budget_uniform_cover
    μ center direction δ θ g b hθ hUnit
    (fun _ r => nonTransverseDirectionIndices direction θ r)
    (fun _ r _ => hNear r)
    hParentSelected
    (fun _ r _ ell hEll =>
      transverse_of_not_mem_nonTransverseDirectionIndices
        direction θ r ell hEll)

end Kakeya.Ninety21
