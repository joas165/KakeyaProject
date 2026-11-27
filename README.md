# KakeyaProject

This branch formalizes the conditional logarithmic endpoint from page 16 of *KakeyaNinety125*. At each large dyadic level, let $R$ be the regular retained labels and let $I_i$ be the original tubes incident to label $i$. Write $R_c$ for the labels with parent $c$.

```math
d(\ell)=\#\{i\in R:\ell\in I_i\}, \qquad
d_c(\ell)=\#\{i\in R_c:\ell\in I_i\}.
```

The hypothesis `TubeFamily.MaxDegreeApplication` assumes

```math
d(\ell)\le\max_{1\le c\le N} d_c(\ell)
```

for every original tube at levels with $q\ge 8$ and ball radius at most $1$. Thus whenever $k\le d(\ell)$ the maximum is at least $k$, and the remainder in the manuscript is empty.

A maximizing parent accounts for every label incident to $\ell$, since its incident labels form a subset of the global incident labels with equal cardinality. Consequently the global ordered tail at $i$ equals the ordered tail along the parent of $i$. The existing fixed-parent angular estimate then applies directly.

The endpoint proof uses this estimate to count the regular pieces, adds the exceptional-piece budget, and sums the dyadic mass bounds. For a tube family with parameter $A$, dimension $n=d+2\ge3$, $N\ge2$, and $p=n/(n-1)$, the conclusion is

```math
\left\|\sum_{\ell=1}^{N}\mathbf 1_{T_\ell^\delta}\right\|_{L^p}
\le C(n,A)(\log N)^{1/p}.
```

Lemma 4.9 and equation (8) are proved by `orderedTail_sum_eq_weighted_degrees`. The proof counts the ordered label pairs incident to each original tube and sums their multiplicity weights.

The degree comparison, remainder identity, tail equality and endpoint theorem are in [Ninety125MaxDegree.lean](Kakeya/Ninety125MaxDegree.lean). The branch endpoint is `TubeFamily.logarithmic_norm_bound_of_maxDegree`.

## Build and audit

The project pins Lean 4.35.0. Run these commands from the repository root.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The [audit](Audit.lean) checks the degree hypothesis and prints the axiom dependencies of the new endpoint.
