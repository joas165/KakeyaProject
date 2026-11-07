# KakeyaProject

KakeyaProject is a Lean 4 formalization of finite Kakeya-style tube estimates.
The library develops dyadic decompositions, finite Vitali selections,
incidence-counting arguments, geometric tube-ball volume bounds, and
conditional endpoint estimates.

## Main results

At each finite level, the generic lemma
`Kakeya.Eighty9.sameBallRepresentative_iff_lowerIncidence_of_parent`
proves that lower incidence is equivalent to representing the parent-based
same-ball relation by one piece per selected tube. This equivalence assumes
finite indices, a surjective parent map, and pairwise-disjoint nonempty pieces.
The numerical row-at-most-one bound follows from that representative
description and disjointness. In the endpoint API, the representative
description for the concrete same-ball relation is exposed as
`SameBallIsRepresentativeAtLevels`, and
`sameBallRowBoundAtLevels_of_representative` proves its row bound.

The endpoint estimates remain conditional on the geometric and selection
data collected in `Kakeya.Eighty9.LocalizedDyadicInputs`, as well as the
applicable per-level incidence condition; this is not an unconditional proof
of the Kakeya conjecture.

Notable declarations include:

- `Kakeya.Eighty9.full_conditional_kakeya_of_lower_incidence` and
  `Kakeya.Eighty9.full_conditional_kakeya_moment_of_lower_incidence`, which
  derive the dyadic budgets and endpoint estimates from per-level lower
  incidence.
- `Kakeya.Eighty9.full_conditional_kakeya_of_composed_range`, which obtains
  lower incidence from range coverage of the composed piece map.
- `Kakeya.Eighty9.full_conditional_kakeya_of_same_ball_representative`, which
  uses the proved representative-row bound; that bound follows from
  `Kakeya.Eighty9.sameBallRowBoundAtLevels_of_representative` and
  pairwise-disjoint pieces.
- `Kakeya.TubeBall.unitTube_ball_volume_le_explicit_arbitrary_direction`,
  which gives an orientation-independent tube-ball volume estimate.

The individual modules cover the conditional moment setup, dyadic levels,
greedy covers and gains, Vitali selection and reindexing, incidence bounds,
and tube-ball geometry. Import `Kakeya` to load the complete library.

## Ninety21 additions

`Kakeya.Ninety21.localized_nonintersecting_bijection` proves the manuscript's
Theorem 4.4 bijection from its finite size and degree hypotheses. The resulting
equivalence fixes the selected indices and assigns distinct nonintersecting
representatives outside the selected family to the remaining pieces.
`Kakeya.Ninety21.intersecting_matching_of_degree_bounds` proves the other Hall
matching argument from the lower and upper degree bounds.

The tube-index counting module proves the row bound directly over distinct
tube indices.

## Build

Install the Lean version in `lean-toolchain`, then run:

```sh
lake build
```

The project pins Mathlib in `lakefile.toml` and `lake-manifest.json`.
GitHub Actions builds and lints the project on pushes and pull requests.
The Mathlib update workflow checks weekly and opens a pull request for a
successful update.

## API documentation

The CI workflow runs doc-gen4 through `docgen-action`. Enable GitHub Pages for
the repository with **GitHub Actions** as the deployment source. The generated
API documentation is then published under the repository's GitHub Pages site.

## License

This project is distributed under the Apache-2.0 license; see [LICENSE](LICENSE).
