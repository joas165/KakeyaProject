# KakeyaProject

Lean 4 formalization of conditional estimates for the Kakeya maximal-function problem. The development includes dyadic decomposition, greedy tube selection, localized tube–ball pieces, Hall reindexing, and finite incidence counting.

**Status:** The analytic endpoint is conditional on geometric and incidence hypotheses. This repository does not establish the unconditional Kakeya conjecture.

## Build

Use the Lean toolchain and dependencies pinned by the repository:

```sh
git clone https://github.com/joas165/KakeyaProject.git
cd KakeyaProject
lake exe cache get
lake build
lake env lean Audit.lean
```

To build the exceptional-budget endpoint alone:

```sh
lake build Kakeya.Ninety21ExceptionalPerLevelEndpoint
```

## Theorem 4.6 counting route

For a finite family of tubes \(T_1^\delta,\dots,T_N^\delta\) in \(\mathbb R^n\), with \(n\ge3\), write \(q=2^m\) and

\[
F_m=\left\{x:q\le\sum_{i=1}^N\mathbf1_{T_i^\delta}(x)<2q\right\}.
\]

The construction uses the same family of retained trimmed pieces throughout. It partitions the remaining pieces into regular and exceptional families, \(\mathcal P_m^{\mathrm{reg}}\) and \(\mathcal P_m^{\mathrm{exc}}\). Selected indices remain original tube indices; exceptional pieces receive **formal auxiliary labels**, not geometric auxiliary tubes.

The regular lower-fiber condition, `hFiberLower`, concerns only the \(N\) original tube indices. When supplied, it gives the conditional counting bound

\[
q|D_m|\le 3N+q|\mathcal P_m^{\mathrm{exc}}|.
\]

## Exceptional per-level bound

`Kakeya/Ninety21ExceptionalPerLevelEndpoint.lean` connects angular packing for unit directions to the exceptional budget at each dyadic level:

\[
q|\mathcal P_m^{\mathrm{exc}}|\le C_{\mathrm{exc}}N.
\]

This estimate uses the stated separation, canonical-radius, total-scale, and concrete retained-family hypotheses. In particular, `ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions` accepts the required angular smallness and direction-population inequalities as inputs.

The parameter-selection lemma `angular_packing_parameters_of_card_bound` replaces those two independent inequalities by a direction-count condition. For \(n=k+2\), assume

\[
0<\varepsilon\le\tfrac12,\qquad N\ge8\cdot5^{n-1}.
\]

Taking \(\theta=\varepsilon\) and \(c=N\varepsilon^{n-1}\) gives

\[
8\cdot5^{n-1}\theta^{n-1}\le c\le N\varepsilon^{n-1}.
\]

`ConcreteGreedyVitaliCandidates.per_level_inputs_of_unit_directions_card_bound` applies this choice. It still requires the other explicit geometric and large-level construction data; the direction-count hypothesis is **not** proved for every configuration.

Combining the exceptional estimate with the conditional regular lower-fiber bound gives

\[
q|D_m|\le(3+C_{\mathrm{exc}})N.
\]

The per-level analytic endpoint uses this uniform count before summing over dyadic levels, so the resulting **conditional** moment estimate has one logarithm from the number of levels. Levels below the large-level cutoff are handled by the finite-mass bound.

## Relevant modules

| File | Role |
| --- | --- |
| `Kakeya/Ninety21ExceptionalPerLevelEndpoint.lean` | Angular parameter selection, exceptional per-level counting, and conditional analytic endpoint. |
| `Kakeya/Ninety21Theorem46Endpoint.lean` | Theorem 4.6 counting and mass-transport interfaces. |
| `Kakeya/Ninety21Theorem46Hall.lean` | Regular representative matching and formal exceptional labels. |
| `Kakeya/Ninety21CompactGreedyPackingIntegration.lean` | Concrete greedy–Vitali geometry and packing inputs. |
| `Audit.lean` | Axiom-dependency checks for selected declarations. |

## Remaining proof obligations

The regular-only `hFiberLower` estimate is deferred. An unconditional endpoint also requires the remaining geometric, normalization, and measure-theoretic hypotheses to be established for the intended tube configurations. A successful Lean build checks the stated theorems **under their explicit hypotheses**.
