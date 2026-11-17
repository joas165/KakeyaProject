# KakeyaProject

**A Lean 4 development of conditional Kakeya maximal-function and tube-sum estimates.**

This repository develops finite incidence combinatorics, greedy tube selection, dyadic decomposition, localized tube–ball geometry, and matching/reindexing arguments for the Kakeya maximal-function problem. The current analytic strategy transports the masses of retained trimmed pieces through a Hall bijection and reduces the desired dyadic count to explicit geometric and incidence obligations.

> **Proof status:** This is a research formalization in progress, **not an unconditional proof of the Kakeya conjecture**.

## Quick start

Install [elan](https://github.com/leanprover/elan) (Lean's toolchain manager) and Git. Clone the project and use the **toolchain pinned by the repository** rather than installing an arbitrary Lean version:

```sh
git clone https://github.com/joas165/KakeyaProject.git
cd KakeyaProject
lake exe cache get
lake build
```

The Mathlib cache step is recommended; building from source is possible but substantially slower. The repository's `lean-toolchain` and Lake dependency manifest determine the reproducible environment. Do not run `lake update` merely to reproduce a reported result, since it may change dependency versions.

To check the concrete integration and inspect selected axiom dependencies:

```sh
lake build Kakeya.Ninety21GreedyVitaliEndpointBridge
lake build Kakeya.Ninety21CompactGreedyPackingIntegration
lake build Kakeya.Ninety21Theorem46Endpoint
lake env lean Audit.lean
```

`lake build` reports the first failing module; an unfinished build is not evidence that the complete endpoint compiles.

## What is being formalized?

For a finite family of narrow tubes \(T_1^\delta,\ldots,T_N^\delta\) in \(\mathbb R^n\), the dyadic multiplicity sets are

\[
F_m=\left\{x: 2^m\le \sum_{i=1}^N\mathbf 1_{T_i^\delta}(x)<2^{m+1}\right\},\qquad q=2^m.
\]

The analysis seeks dyadic volume and moment estimates at the Kakeya exponent \(p=n/(n-1)\). Its inputs include geometric localization of the level sets, a greedy selection of trimmed tubes, and an incidence count for the retained pieces. The relevant asymptotic regime has \(N\asymp \delta^{1-n}\), with \(\delta\)-separated directions.

The Theorem 4.6 route works with **actual retained trimmed pieces**, not merely their parent tubes. A trimmed piece has a unique parent, but one original **untrimmed** tube may meet multiple different retained pieces. These statements must not be conflated.

### Main proof route

1. **Dyadic reduction.** Convert the tube-sum moment into estimates on the levels \(F_m\).
2. **Greedy selection and localization.** Keep selected pieces and remaining localized trimmed pieces, with a mass-capture comparison.
3. **Geometric classification.** For each remaining piece \(P\), count the original tubes it meets:
   \[
   d(P)=\#\{i\in\{1,\dots,N\}:P\cap T_i^\delta\ne\varnothing\}.
   \]
   Regular pieces satisfy \(2d(P)\le N\); exceptional pieces satisfy \(2d(P)>N\).
4. **Theorem 4.6 reindexing.** Selected tube indices remain fixed. Regular pieces are assigned distinct **nonintersecting original-tube representative labels** outside the selected family; exceptional pieces are assigned separate auxiliary labels. A label represents the same source piece and is **not** asserted to be a tube containing it.
5. **Exact mass transport and conditional counting.** A bijection changes the indexing of the source masses without changing their sum. A regular-only lower-fiber condition yields the double count; exceptional pieces retain a separate overhead term.

For large levels, the representative label type is the disjoint union of original tube labels and exceptional auxiliary labels. For the pair-indexed construction in dimensions \(n\ge3\), the analytic cutoff is

\[
Q_0=\max\{8,(8C_{\mathrm{pack}})^2\}.
\]

The Hall construction and regular-piece budget apply above this cutoff. Levels \(q<Q_0\), including the intermediate range above 8, use the finite ambient-mass estimate in the analytic endpoint.

### Greedy–Vitali and concrete bounds integration

The concrete integration constructs a maximal-unused greedy selection of original tube indices. Each stage maximizes the residual gain among as-yet-unused tubes. The first \(\lceil N/q\rceil\) selected indices are distinct, and the associated residual-mass recurrence is derived from maximality and dyadic multiplicity. The selected-tube budget follows from this construction.

Finite-center nets localize the selected greedy gains. The occupied Vitali construction covers the gains using radius-\(R_m\) balls and their triple-radius enlargements. Empty gains contribute no occupied centers. In `ofGreedyNetFamilyAllowEmpty`, the final ball index type uses only active tube–center pairs; **there is no auxiliary fallback ball** to satisfy a nonempty index type.

The Euclidean bounds integration provides occupied-ball and retained-piece nonemptiness, selected-cardinality bounds, the canonical radius

\[
R_m=Aq^{-1/(n-1)},
\]

and the tube–ball mass estimate of the form

\[
\mu(P_s)\le C\delta^{n-1}R_m.
\]

`ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused` derives the dyadic-scale and selected-cardinality fields from the construction. `ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclidean` passes those bounds, the greedy recurrence, and the triple-radius estimate to the existing two-radius analytic interface.

The parent-associated ball bound is derived from the actual tube-wise Vitali selection. For each selected parent tube, its selected radius-\(R_m\) balls are pairwise disjoint and meet that tube. The length-one tube geometry gives

\[
\#\{i:\text{a retained label has parent }r\text{ and ball index }i\}
\le C_{\mathrm{pack}}q^{1/(n-1)}.
\]

This is the `hHallRight` field used by the localized construction. It counts balls associated with the specified parent tube; it is not a count of all balls from every parent that happen to intersect that tube. Disjointness is used within each parent's Vitali selection.

`ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnusedGeometry` derives this bound using the canonical radius and the total-scale condition \(\delta N^{1/(n-1)}\le A\). The compact specialization, `euclideanBoundsOfCompactMaximalUnusedGeometry`, also supplies the center, radius, and selected-family identifications. `ConcreteTwoRadiusGreedy.ofCompactMaximalUnusedGeometry` supplies the chosen-sequence identification and connects the construction to the two-radius analytic interface.

The compact constructors still take the normalization \(N\delta^{n-1}\le Z\), the total-scale condition, boundedness of the dyadic bands, measurability and unit-direction hypotheses, and domination of the finite measure by Euclidean volume. A final Euclidean application must supply these inputs with suitable dimension-dependent constants.

The greedy–Vitali specialization uses identity trimming for its localized gains. Applying the Theorem 4.6 endpoint requires the matching, mass comparison, and counting estimates for the same retained family throughout.

## Key equalities and open bound

Let \(B_m\) be the selected indices, \(\mathcal P_m\) the remaining retained pieces, and \(\mathcal P_m^{\mathrm{reg}}\sqcup\mathcal P_m^{\mathrm{exc}}\) their degree-defined partition. The Theorem 4.6 construction gives a bijective relabeling of **the same source family**:

\[
\Phi_m:\;B_m\sqcup\bigl(\mathcal P_m^{\mathrm{reg}}\sqcup\mathcal P_m^{\mathrm{exc}}\bigr)\xrightarrow{\ \sim\ }D_m.
\]

Using \(E_r\) for the source piece retrieved through \(\Phi_m^{-1}\), its mass is preserved exactly:

\[
\sum_{r\in D_m}\mu(E_r)
=\sum_{s\in B_m\sqcup\mathcal P_m}\mu(E_s).
\]

This is a change of labels, not an estimate of intersections with the assigned representative tubes.

The **postponed Theorem 4.6 regular lower-fiber condition** counts the **\(N\) original tube indices only**:

\[
\forall r\in\sigma(\mathcal P_m^{\mathrm{reg}}),\qquad
\#\{\ell\in\{1,\ldots,N\}:\widehat\Phi_m(\ell)=r\}\ge 2^m.
\]

Here \(\widehat\Phi_m\) is a single-valued *partial assignment* to regular labels (represented by `Option` in Lean). It does not assume that original tube–piece intersections are unique. **Auxiliary labels are purely formal representatives of exceptional pieces.** They have no geometric tubes and do not contribute to these fibers. All original-tube geometry and incidence counting use the original \(N\) indices.

Under this condition, the regular-piece double count gives \(q|\mathcal P_m^{\mathrm{reg}}|\le N\). Combining it with the greedy selected-tube budget and the cardinality identity yields the displayed conditional estimate

\[
q|D_m|\le 3N+q|\mathcal P_m^{\mathrm{exc}}|.
\]

The endpoint records the exceptional contribution through

\[
E_{\mathrm{exc}}=\sum_m 2^m|\mathcal P_m^{\mathrm{exc}}|.
\]

The current endpoint uses this total overhead to bound each level's exceptional term. Its concrete geometric control remains to be supplied. The parent-associated `hHallRight` estimate and the exceptional packing estimate are separate parts of the argument.

## Finding your way around the code

| Path | Role |
| --- | --- |
| [`Kakeya.lean`](Kakeya.lean) | Top-level import root for the library. |
| [`Kakeya/ConditionalKakeya.lean`](Kakeya/ConditionalKakeya.lean) and [`Kakeya/FinalTubeSum.lean`](Kakeya/FinalTubeSum.lean) | Analytic setup and tube-sum endpoint infrastructure. |
| [`Kakeya/Eighty9GreedyGain.lean`](Kakeya/Eighty9GreedyGain.lean), [`Kakeya/Eighty9GreedyCover.lean`](Kakeya/Eighty9GreedyCover.lean), [`Kakeya/Eighty9GeometryDischarges.lean`](Kakeya/Eighty9GeometryDischarges.lean) | Greedy selection, coverage, and geometric/mass interfaces. |
| [`Kakeya/Eighty9ArbitraryOrientationTubeBall.lean`](Kakeya/Eighty9ArbitraryOrientationTubeBall.lean), [`Kakeya/Eighty9FiniteVitali.lean`](Kakeya/Eighty9FiniteVitali.lean) | Tube–ball geometry and Vitali covering infrastructure. |
| [`Kakeya/Ninety21GreedyVitaliIntegration.lean`](Kakeya/Ninety21GreedyVitaliIntegration.lean) | Maximal-unused selection, finite gain nets, occupied Vitali candidates, empty-gain handling, and greedy recurrence. |
| [`Kakeya/Ninety21GreedyVitaliBounds.lean`](Kakeya/Ninety21GreedyVitaliBounds.lean) | Occupancy and selected-cardinality lemmas, canonical radius, and Euclidean retained-piece volume estimates. |
| [`Kakeya/Ninety21GreedyVitaliEndpointBridge.lean`](Kakeya/Ninety21GreedyVitaliEndpointBridge.lean) | Derived dyadic bounds and direct connection to the conditional two-radius endpoint. |
| [`Kakeya/Ninety21OriginalTubeBallPacking.lean`](Kakeya/Ninety21OriginalTubeBallPacking.lean) and [`Kakeya/Ninety21ParentVitaliPacking.lean`](Kakeya/Ninety21ParentVitaliPacking.lean) | Euclidean packing and its application to parent-associated Vitali balls. |
| [`Kakeya/Ninety21GeometricPackingEndpoint.lean`](Kakeya/Ninety21GeometricPackingEndpoint.lean) | Canonical radius bounds, derived parent-associated packing, and geometric endpoint constructors. |
| [`Kakeya/Ninety21CompactGreedyPackingIntegration.lean`](Kakeya/Ninety21CompactGreedyPackingIntegration.lean) | Compact maximal-unused identifications and concrete geometric constructors. |
| [`Kakeya/Ninety21RegularBudget.lean`](Kakeya/Ninety21RegularBudget.lean) | Regular-piece budget from pair indexing and parent-associated ball counts above the analytic cutoff. |
| [`Kakeya/Ninety21Bijection.lean`](Kakeya/Ninety21Bijection.lean) | Finite Hall matching and bijection-extension tools. |
| [`Kakeya/Ninety64TrimmedBijection.lean`](Kakeya/Ninety64TrimmedBijection.lean) | Matching statements for actual trimmed pieces; elementary exceptional-piece counts. |
| [`Kakeya/Ninety21ConcreteIntegration.lean`](Kakeya/Ninety21ConcreteIntegration.lean) | Retained source-family data and legacy Theorem 4.2 reindexing (`hallEquiv42`). |
| [`Kakeya/Ninety21PaperDoubleCount.lean`](Kakeya/Ninety21PaperDoubleCount.lean) | Geometric regular/exceptional split and finite original-tube fiber double counting. |
| [`Kakeya/Ninety21Theorem46Hall.lean`](Kakeya/Ninety21Theorem46Hall.lean) | Theorem 4.6 nonintersecting representative map, with exceptional auxiliary labels. |
| [`Kakeya/Ninety21Theorem46Endpoint.lean`](Kakeya/Ninety21Theorem46Endpoint.lean) | Mass transport, conditional dyadic budget, and analytic endpoint integration. |
| [`Audit.lean`](Audit.lean) | `#print axioms` checks for selected formal statements. |

The development includes additional `Eighty*` and `Ninety*` modules documenting intermediate variants. **Module presence does not mean a theorem is part of the current final proof path.** For the Theorem 4.6 counting route, begin with `Ninety21Theorem46Endpoint.lean`; for the concrete greedy–Vitali geometric construction, begin with `Ninety21CompactGreedyPackingIntegration.lean` and follow its imports backward.

### Useful theorem and constructor names

- `Kakeya.Ninety21.maximalUnusedDyadicSelected_card`: cardinality of the first greedy selections.
- `Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty_zero_balls`: empty center families give no indexed balls.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_piece_euclidean_cost`: geometric volume bound for retained localized pieces.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused`: derived concrete bounds constructor.
- `Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclidean`: concrete two-radius endpoint constructor.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.selected_card_le_of_canonical_geometry`: tube-wise Vitali packing at the canonical radius.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.compactMaximalUnused_identifications`: center, selected-family, and chosen-sequence identifications.
- `Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofCompactMaximalUnusedGeometry`: compact geometric constructor for the two-radius interface.
- `Kakeya.Ninety21.paper46Construction_of_pair_indexing_at_cutoff`: Hall construction data with the derived regular-piece budget.
- `Kakeya.Ninety21.paper46_analytic_mass_sum`: equality of the source and Theorem 4.6 reindexed mass sums.
- `Kakeya.Ninety21.paper46_analytic_capture`: transfers the existing greedy mass comparison to those representative labels.
- `Kakeya.Ninety21.paper46_analytic_count_with_exceptional`: double-counting bound retaining exceptional overhead.
- `Kakeya.Ninety21.full_conditional_kakeya_moment_of_paper46`: conditional moment endpoint.
- `Kakeya.Ninety21.full_conditional_kakeya_of_paper46`: conditional norm endpoint.

## Proof and verification status

The formalization separates (a) finite combinatorial lemmas and changes of indexing, (b) conditional analytic consequences, and (c) the geometric hypotheses required to apply them to the Kakeya configuration.

| Component | Current status |
| --- | --- |
| Dyadic decomposition, finite matching infrastructure, and abstract mass-sum reindexing | Implemented in existing Lean modules. |
| Maximal-unused greedy selection, occupied Vitali localization, empty-gain indexing, and residual recurrence | Integrated into the concrete construction. |
| Euclidean piece volume, selected-cardinality and dyadic-radius bounds | Provided by the concrete bounds modules under their stated geometric hypotheses. |
| Parent-associated `hHallRight` and compact identifications | Derived for the canonical tube-wise Vitali construction under the stated Euclidean and scale hypotheses. |
| Derived bounds and two-radius analytic interface | Connected by the compact geometric constructor; normalization, total scale, measure and boundedness inputs remain explicit. |
| Theorem 4.6 regular/exceptional labels and mass transport | Integrated into the conditional endpoint. |
| Regular-piece cardinality input (`Paper46ConstructionData.hRegularBudget`) | Derived from localized parent-associated ball counts and pair indexing above the cutoff; constructors supply it to the Hall data. |
| Exceptional Vitali-ball packing for the concrete retained family | The elementary counting bridge exists; the complete geometric application remains open. |
| Regular lower-fiber estimate (`hFiberLower`) | Postponed; counts original tube indices and regular pieces only. |
| Full unconditional Kakeya maximal-function conjecture | **Not proved by this repository's present conditional endpoint.** |

The earlier `hallEquiv42` is an *intersection-compatible* matching into original tube indices. It is not interchangeable with the Theorem 4.6 `hallEquiv`, whose regular representatives are *nonintersecting* and whose exceptional representatives are auxiliary labels.

No argument in the current intended proof route may rely on `hParentInjective`, `TubeWiseUnique`, `hPaperRow`, or \(|\mathcal P_m|\le|B_m|\). In particular, unique ownership of a trimmed piece is **not** an upper bound on how many retained pieces an original tube may intersect.

## Building and auditing changes

For incremental development:

```sh
lake build Kakeya.Ninety21GreedyVitaliIntegration
lake build Kakeya.Ninety21GreedyVitaliBounds
lake build Kakeya.Ninety21GreedyVitaliEndpointBridge
lake build Kakeya.Ninety21CompactGreedyPackingIntegration
lake build Kakeya.Ninety21PaperDoubleCount
lake build Kakeya.Ninety21Theorem46Hall
lake build Kakeya.Ninety21Theorem46Endpoint
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the axiom dependencies of audited declarations. A zero-error build demonstrates that Lean has checked the declarations **under their written hypotheses**; it does not discharge assumptions appearing in theorem statements or structure fields.

If a build fails, report the first `error:` location, the module name, and the pinned Lean version; avoid attributing downstream missing `.olean` errors to independent mathematical problems.

## Roadmap

The construction and direct endpoint integration are implemented conditionally. Remaining mathematical and geometric work:

1. Prove the regular-only original-tube `hFiberLower` condition for the assignment and retained family used by Theorem 4.6.
2. Prove the exceptional packing estimate for that family and control the exceptional overhead used by the analytic endpoint.
3. Instantiate the Theorem 4.6 endpoint with the concrete retained geometry, its pair indexing, mass comparison, regular fibers, and exceptional estimate.
4. Derive dimension-dependent normalization and total-scale bounds from direction separation, supply the concrete measure and boundedness inputs, and complete the passage to the unconditional maximal-function statement.

This is an evolving formal research project. Corrections to statement scope, proofs, and the boundary between hypotheses and established theorems are welcome as GitHub issues or pull requests. When proposing changes, state which exact Lean declaration is affected and whether `lake build` succeeds on the repository's pinned toolchain.
