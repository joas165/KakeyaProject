# KakeyaProject

KakeyaProject is a Lean 4 formalization of finite Kakeya-style tube estimates.
The library develops dyadic decompositions, finite Vitali selections,
incidence-counting arguments, geometric tube-ball volume bounds, and
conditional endpoint estimates.

## Main results

The endpoint estimates are conditional on the geometric and selection data
collected in `Kakeya.Eighty9.LocalizedDyadicInputs`. In particular, the
lower-incidence and representative-row hypotheses are stated explicitly;
the project does not claim an unconditional Kakeya conjecture result.

Notable declarations include:

- `Kakeya.Eighty9.full_conditional_kakeya_of_lower_incidence` and
  `Kakeya.Eighty9.full_conditional_kakeya_moment_of_lower_incidence`, which
  derive the dyadic budgets and endpoint estimates from per-level lower
  incidence.
- `Kakeya.Eighty9.full_conditional_kakeya_of_composed_range`, which obtains
  lower incidence from range coverage of the composed piece map.
- `Kakeya.Eighty9.full_conditional_kakeya_of_same_ball_representative`, which
  derives the row bound from the explicitly required representative condition.
- `Kakeya.TubeBall.unitTube_ball_volume_le_explicit_arbitrary_direction`,
  which gives an orientation-independent tube-ball volume estimate.

The individual modules cover the conditional moment setup, dyadic levels,
greedy covers and gains, Vitali selection and reindexing, incidence bounds,
and tube-ball geometry. Import `Kakeya` to load the complete library.

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
