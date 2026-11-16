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

For large levels, the representative label type is the disjoint union of original tube labels and exceptional auxiliary labels. The small levels \(q<8\) use a separate finite cardinality bound because Theorem 4.6 has the hypothesis \(q\ge8\).

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

**The concrete bridge remains conditional.** It takes the tube-count normalization \(N\delta^{n-1}\le Z\) and an original-tube *ball-incidence* estimate

\[
\#\{i:B_{m,i}\cap T_r^\delta\ne\varnothing\}\le Kq^{1/(n-1)}.
\]

It also requires compatibility data identifying the chosen sequence, canonical radii, occupied centers, and selected family with the constructed geometry. These are explicit inputs where the bridge does not derive them automatically. The ball-incidence bound is distinct from the regular-piece lower-fiber condition in Theorem 4.6.

The greedy–Vitali specialization uses identity trimming for its localized gains. Its construction alone does **not** establish identification with every nontrivially trimmed source family used in the Theorem 4.6 route.

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

Here \(\widehat\Phi_m\) is a single-valued *partial assignment* to regular labels (represented by `Option` in Lean). It does not assume that original tube–piece intersections are unique. **Auxiliary labels do not contribute to these fibers**: their associated tubes can lie outside \(B(0,2)\) and need not intersect any retained piece.

Under this condition, the regular-piece double count gives \(q|\mathcal P_m^{\mathrm{reg}}|\le N\). Combining it with the greedy selected-tube budget and the cardinality identity yields the displayed conditional estimate

\[
q|D_m|\le 3N+q|\mathcal P_m^{\mathrm{exc}}|.
\]

The exceptional contribution is recorded, not silently discarded. A geometric packing argument is needed to control it before the desired uniform analytic estimate follows.

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
| [`Kakeya/Ninety21Bijection.lean`](Kakeya/Ninety21Bijection.lean) | Finite Hall matching and bijection-extension tools. |
| [`Kakeya/Ninety64TrimmedBijection.lean`](Kakeya/Ninety64TrimmedBijection.lean) | Matching statements for actual trimmed pieces; elementary exceptional-piece counts. |
| [`Kakeya/Ninety21ConcreteIntegration.lean`](Kakeya/Ninety21ConcreteIntegration.lean) | Retained source-family data and legacy Theorem 4.2 reindexing (`hallEquiv42`). |
| [`Kakeya/Ninety21PaperDoubleCount.lean`](Kakeya/Ninety21PaperDoubleCount.lean) | Geometric regular/exceptional split and finite original-tube fiber double counting. |
| [`Kakeya/Ninety21Theorem46Hall.lean`](Kakeya/Ninety21Theorem46Hall.lean) | Theorem 4.6 nonintersecting representative map, with exceptional auxiliary labels. |
| [`Kakeya/Ninety21Theorem46Endpoint.lean`](Kakeya/Ninety21Theorem46Endpoint.lean) | Mass transport, conditional dyadic budget, and analytic endpoint integration. |
| [`Audit.lean`](Audit.lean) | `#print axioms` checks for selected formal statements. |

The development includes additional `Eighty*` and `Ninety*` modules documenting intermediate variants. **Module presence does not mean a theorem is part of the current final proof path.** For the Theorem 4.6 counting route, begin with `Ninety21Theorem46Endpoint.lean`; for the concrete greedy–Vitali analytic interface, begin with `Ninety21GreedyVitaliEndpointBridge.lean` and follow their imports backward.

### Useful theorem and constructor names

- `Kakeya.Ninety21.maximalUnusedDyadicSelected_card`: cardinality of the first greedy selections.
- `Kakeya.Ninety21.ConcreteTubeBallGeometry.ofGreedyNetFamilyAllowEmpty_zero_balls`: empty center families give no indexed balls.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.retained_piece_euclidean_cost`: geometric volume bound for retained localized pieces.
- `Kakeya.Ninety21.ConcreteGreedyVitaliCandidates.euclideanBoundsOfMaximalUnused`: derived concrete bounds constructor.
- `Kakeya.Ninety21.ConcreteTwoRadiusGreedy.ofDerivedMaximalUnusedEuclidean`: concrete two-radius endpoint constructor.
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
| Derived bounds and two-radius analytic interface | Integrated conditionally; normalization, original-tube ball incidence, and compatibility data remain explicit inputs. |
| Theorem 4.6 regular/exceptional labels and mass transport | Integrated into the conditional endpoint. |
| Regular-piece cardinality input (`Paper46ConstructionData.hRegularBudget`) | Not yet discharged from the concrete geometric setup. |
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

1. Derive original-tube ball incidence (`hHallRight`) from the appropriate indexed geometric family; obtain tube-count normalization from direction-separation and packing, and discharge any remaining compatibility conditions.
2. Prove the regular-piece incidence/cardinality obligations for the actual Theorem 4.6 retained family, including the regular-only original-tube `hFiberLower` condition.
3. Prove the exceptional Vitali-ball packing estimate and control the exceptional overhead.
4. Connect these geometric inputs to the full unconditional maximal-function estimate, without changing the source family during matching and counting.

This is an evolving formal research project. Corrections to statement scope, proofs, and the boundary between hypotheses and established theorems are welcome as GitHub issues or pull requests. When proposing changes, state which exact Lean declaration is affected and whether `lake build` succeeds on the repository's pinned toolchain.
