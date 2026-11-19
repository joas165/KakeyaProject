module

public import Kakeya.Ninety21AngularCapCounting

/-!
# Counting separated directions in two projected spherical caps

A two-sheeted Lipschitz chart over an `(n-1)`-dimensional Euclidean ball
reduces the near-direction count to a finite Euclidean net.
-/

@[expose] public section

namespace Kakeya.Ninety21

attribute [local instance] Classical.propDecidable

/-- An `ε`-separated finite family with two Lipschitz graph charts over
an `(n-1)`-dimensional ball has at most twice the cardinality of a
radius-`ε/8` net of the projected ball. -/
theorem separated_two_chart_card_le
    {n : ℕ} {I : Type*}
    (point : I → Kakeya.Space n)
    (projection : I → Kakeya.Space (n - 1))
    (side : I → Bool) (J : Finset I)
    (ε : ℝ) (hε : 0 < ε)
    (Z : Finset (Kakeya.Space (n - 1)))
    (hSeparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      ε ≤ dist (point i) (point j))
    (hNet : ∀ i ∈ J, ∃ z ∈ Z,
      dist (projection i) z < ε / 8)
    (hReverse : ∀ i ∈ J, ∀ j ∈ J, side i = side j →
      dist (point i) (point j) ≤
        2 * dist (projection i) (projection j)) :
    J.card ≤ 2 * Z.card := by
  classical
  let pick : {i : I // i ∈ J} → Bool ×
      {z : Kakeya.Space (n - 1) // z ∈ Z} :=
    fun i => (side i.val,
      ⟨Classical.choose (hNet i.val i.property),
       (Classical.choose_spec (hNet i.val i.property)).1⟩)
  have hpick : Function.Injective pick := by
    intro i j hEq
    apply Subtype.ext
    by_contra hij
    have hSide : side i.val = side j.val :=
      congrArg Prod.fst hEq
    have hZ : (pick i).2.val = (pick j).2.val :=
      congrArg (fun p : Bool × {z : Kakeya.Space (n - 1) // z ∈ Z} => p.2.val) hEq
    have hi : dist (projection i.val) (pick i).2.val < ε / 8 :=
      (Classical.choose_spec (hNet i.val i.property)).2
    have hj : dist (projection j.val) (pick j).2.val < ε / 8 :=
      (Classical.choose_spec (hNet j.val j.property)).2
    have hProj : dist (projection i.val) (projection j.val) < ε / 4 := by
      have ht := dist_triangle (projection i.val) (pick i).2.val (projection j.val)
      have hj' : dist (pick i).2.val (projection j.val) < ε / 8 := by
        rw [hZ, dist_comm]
        exact hj
      linarith
    have hReverse' := hReverse i.val i.property j.val j.property hSide
    have hSep := hSeparated i.val i.property j.val j.property hij
    linarith
  have hc := Fintype.card_le_of_injective pick hpick
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] using hc

/-- A single half-radius net covers the projected ball, uniformly over
all parent directions. -/
theorem uniform_projected_cap_net
    (n : ℕ) (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 ≤ θ) :
    ∃ L : ℕ,
      ∀ projection : Kakeya.Space (n - 1) → Prop,
        (∀ w, projection w → ‖w‖ ≤ θ) →
        ∃ Z : Finset (Kakeya.Space (n - 1)), Z.card ≤ L ∧
          ∀ w, projection w → ∃ z ∈ Z, dist w z < ε / 8 := by
  have hD : 0 ≤ 4 * θ / ε := by positivity
  obtain ⟨L, hCover⟩ :=
    euclidean_uniform_half_radius_net (n - 1) (4 * θ / ε) hD
  refine ⟨L, ?_⟩
  intro projection hSmall
  obtain ⟨Z, hZ, hZCover⟩ :=
    hCover (ε / 4) (by positivity) (0 : Kakeya.Space (n - 1))
  refine ⟨Z, hZ, ?_⟩
  intro w hw
  have hn := hSmall w hw
  have hw0 : dist w (0 : Kakeya.Space (n - 1)) ≤ θ := by
    simpa only [dist_zero_right] using hn
  have heq : (4 * θ / ε) * (ε / 4) = θ := by
    field_simp [ne_of_gt hε] <;> ring
  have hwBound : dist w (0 : Kakeya.Space (n - 1)) ≤
      (4 * θ / ε) * (ε / 4) := by
    simpa only [heq] using hw0
  obtain ⟨z, hzZ, hzDist⟩ := hZCover w hwBound
  refine ⟨z, hzZ, ?_⟩
  have hRadius : ε / 4 / 2 = ε / 8 := by ring
  simpa only [hRadius] using hzDist

/-- Near directions lie in two Lipschitz charts of the orthogonal
hyperplane; a projected net therefore bounds the cardinal of each
nontransverse direction family. -/
theorem nonTransverseDirectionIndices_card_of_projected_charts
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (side : T → T → Bool)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hProjSmall : ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ)
    (hReverse : ∀ r i j : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
      j ∈ nonTransverseDirectionIndices direction θ r →
      side r i = side r j →
      dist (direction i) (direction j) ≤
        2 * dist (projection r i) (projection r j)) :
    ∃ L : ℕ, ∀ r : T,
      (nonTransverseDirectionIndices direction θ r).card ≤ 2 * L := by
  classical
  obtain ⟨L, hNet⟩ := uniform_projected_cap_net n ε θ hε hθ
  refine ⟨L, ?_⟩
  intro r
  let J := nonTransverseDirectionIndices direction θ r
  obtain ⟨Z, hZ, hZNet⟩ := hNet
    (fun w => ∃ i ∈ J, projection r i = w)
    (by
      intro w hw
      obtain ⟨i, hi, hwi⟩ := hw
      rw [← hwi]
      exact hProjSmall r i hi)
  have hPointsNet : ∀ i ∈ J,
      ∃ z ∈ Z, dist (projection r i) z < ε / 8 := by
    intro i hi
    exact hZNet (projection r i) ⟨i, hi, rfl⟩
  have hCard := separated_two_chart_card_le
    direction (projection r) (side r) J ε hε Z
    (by
      intro i _ j _ hij
      exact hSeparated i j hij)
    hPointsNet
    (by
      intro i hi j hj hSame
      exact hReverse r i j hi hj hSame)
  change (nonTransverseDirectionIndices direction θ r).card ≤ 2 * Z.card at hCard
  omega

/-- A population bound converts the projected two-cap estimate into
`hNear`, for the actual original tube indices. -/
theorem nonTransverseDirectionIndices_budget_of_projected_charts
    {n : ℕ} {T : Type*} [Fintype T]
    (direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (side : T → T → Bool)
    (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 ≤ θ)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hProjSmall : ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ)
    (hReverse : ∀ r i j : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
      j ∈ nonTransverseDirectionIndices direction θ r →
      side r i = side r j →
      dist (direction i) (direction j) ≤
        2 * dist (projection r i) (projection r j)) :
    ∃ L : ℕ,
      (8 * L ≤ Fintype.card T →
        ∀ r : T,
          4 * (nonTransverseDirectionIndices direction θ r).card ≤
            Fintype.card T) := by
  obtain ⟨L, hCard⟩ :=
    nonTransverseDirectionIndices_card_of_projected_charts
      direction projection side ε θ hε hθ
      hSeparated hProjSmall hReverse
  refine ⟨L, ?_⟩
  intro hPop r
  have h := hCard r
  omega


/-- Exceptional-piece counting from a two-sheeted projected cap chart.
The population inequality is stated for the net cardinal produced by
Euclidean compactness. -/
theorem ConcreteGreedyVitaliCandidates.exceptional_scaled_budget_of_projected_chart
    {n : ℕ} {T : Type*} [Fintype T]
    (μ : MeasureTheory.Measure (Kakeya.Space n))
    (center direction : T → Kakeya.Space n)
    (projection : T → T → Kakeya.Space (n - 1))
    (side : T → T → Bool)
    (δ θ ε : ℝ)
    (g : ConcreteTubeBallGeometry
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ))
    (d : ConcreteGreedyVitaliCandidates
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) g)
    (b : ConcreteTubeBallBounds μ
      (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n d.retained)
    (hθ : 0 < θ) (hε : 0 < ε)
    (hUnit : ∀ r, ‖direction r‖ = 1)
    (hSeparated : ∀ i j : T, i ≠ j →
      ε ≤ dist (direction i) (direction j))
    (hProjSmall : ∀ r i : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
        ‖projection r i‖ ≤ θ)
    (hReverse : ∀ r i j : T,
      i ∈ nonTransverseDirectionIndices direction θ r →
      j ∈ nonTransverseDirectionIndices direction θ r →
      side r i = side r j →
      dist (direction i) (direction j) ≤
        2 * dist (projection r i) (projection r j))
    (hParentSelected : ∀ m r,
      r ∈ (d.retained.toBallLocalized μ n b).B m → r ∈ g.B m) :
    ∃ A : ℕ, 8 * A ≤ Fintype.card T →
      ∃ L : ℕ, ∀ m : Kakeya.Eighty4.DyadicIndex (Fintype.card T),
        δ ≤ d.radius m →
        Kakeya.Eighty4.dyadicScale (Fintype.card T) m *
          ((paperExceptionalPieces μ
            (fun ell => Kakeya.unitTube (center ell) (direction ell) δ) n
            (d.retained.toBallLocalized μ n b).toRetainedDyadicData m).card : ℝ) ≤
          8 * (L : ℝ) * (Fintype.card T : ℝ) := by
  obtain ⟨A, hCapBudget⟩ :=
    nonTransverseDirectionIndices_budget_of_projected_charts
      direction projection side ε θ hε hθ.le
      hSeparated hProjSmall hReverse
  refine ⟨A, ?_⟩
  intro hPopulation
  have hNear := hCapBudget hPopulation
  exact d.exceptional_scaled_budget_uniform_cover
    μ center direction δ θ g b hθ hUnit
    (fun _ r => nonTransverseDirectionIndices direction θ r)
    (fun _ r _ => hNear r)
    hParentSelected
    (fun _ r _ ell hEll =>
      transverse_of_not_mem_nonTransverseDirectionIndices
        direction θ r ell hEll)

end Kakeya.Ninety21
