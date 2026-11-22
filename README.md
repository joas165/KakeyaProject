# KakeyaProject

A Lean 4 formalization of dyadic estimates for the Kakeya maximal-function problem. This branch proves a conditional logarithmic endpoint for the project's unit-length Euclidean cylinders. **The only unproved estimate in the endpoint is the ordered overlap inequality used in the application of Lemma 4.8.**

## Endpoint theorem

Let $n\ge 3$, $p=n/(n-1)$, and let $T_1^\delta,\ldots,T_N^\delta$ be unit-length cylinders of radius $\delta>0$ in $\mathbb R^n$, with $N\ge 2$. Their unit direction vectors satisfy $\lVert v_i-v_j\rVert\ge\delta$ for $i\ne j$. Fix $A>0$ with $\delta N^{1/(n-1)}\le A$. Write $M(x)=\sum_{i=1}^N\mathbf 1_{T_i^\delta}(x)$.

Under the Lemma 4.8 application below, `Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound` proves

$$
\lVert M\rVert_{L^p(\mathbb R^n)}
\le C(n,A,K)\,(\ln N)^{(n-1)/n}.
$$

The constant is uniform in $N$ and $\delta$ for fixed $n,A,K$. In Lean the dimension is written as $n=d+2$, with $d\ge1$.

## Exact application of Lemma 4.8

Set $q=2^m$, $F_m=\{x:q\le M(x)<2q\}$, and $\rho=Aq^{-1/(n-1)}$. At each level with $q\ge8$ and $\rho\le1$, let $B$ be the greedy-selected parent tube indices. A retained piece $P_i$ is the intersection of its parent's greedy gain with the selected ball enlarged to radius $3\rho$. Define its incidence set using the original tubes,

$$
I_i=\{\ell\in\{1,\ldots,N\}:T_\ell^\delta\cap P_i\ne\varnothing\}.
$$

After accounting for the selected parent labels, let $R$ index the remaining pieces with $2|I_i|\le N$. For each $c\in B$, let $R_c$ contain the labels in $R$ with parent $c$. Order the labels by greedy parent selection and then by ball index within each parent.

The assumption `TubeFamily.OverlapApplication K` is the following inequality, with the **same** $K\ge0$ at every such level.

$$
\sum_{c\in B}\sum_{i\in R_c}
  \sum_{\substack{j\in R\\i<j}} |I_i\cap I_j|
\;\le\;
K\sum_{c\in B}\sum_{i\in R_c}|I_i|.
$$

The inner sum includes every later regular label, including labels with a different parent. Lean proves the fixed-parent overlap estimate in Lemma 4.8. Its application to the displayed sum is the conditional step on page 15 of the manuscript.

## From overlap to the endpoint

Each regular piece contains a point of $F_m$, so $q\le |I_i|$. Counting first and second moments of the incidence degrees, then applying Cauchy–Schwarz, gives $q|R|\le (1+2K)N$. For the exceptional pieces, which satisfy $2|I_i|>N$, the formalization applies the proved fixed-parent estimate separately within each parent class. Adding the greedy parent count gives an $O_{n,A,K}(N/q)$ bound for the complete retained family.

The same triple-radius pieces cover the greedy gains and enter the piece-volume estimate. Their count and mass capture give a uniform bound on $q^p|F_m|$. The remaining small levels use the finite-volume estimate. Summing the dyadic levels gives the logarithmic moment bound and taking the $p$th root gives the endpoint above.

## Build and check

From a checkout of this branch, use the pinned Lean 4.35.0 toolchain. To fetch the mathlib cache and build the endpoint module, run

```sh
lake exe cache get
lake build Kakeya.Ninety109Endpoint
```

Run `lake build` for the whole project. To inspect the endpoint signature and its axiom dependencies, run this in a Lean file in the project.

```lean
import Kakeya.Ninety109Endpoint

#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound
```

The axiom check reports `propext`, `Classical.choice`, and `Quot.sound`. The overlap assumption appears explicitly as the argument `happ : f.OverlapApplication K` in the theorem signature.

## Source files

| Module | Contents |
| --- | --- |
| [Ninety109FixedParentOverlap](Kakeya/Ninety109FixedParentOverlap.lean) | Fixed-parent geometry, the ordered overlap inequality, and the incidence second-moment estimate |
| [Ninety109RegularPieceCount](Kakeya/Ninety109RegularPieceCount.lean) | Regular-piece count from the overlap application |
| [Ninety109RetainedCover](Kakeya/Ninety109RetainedCover.lean) | Triple-radius retained pieces and coverage of the greedy gains |
| [Ninety109ExceptionalCount](Kakeya/Ninety109ExceptionalCount.lean) | Exceptional-piece count at each relevant level |
| [Ninety109TubeFamily](Kakeya/Ninety109TubeFamily.lean) | Euclidean tube family, canonical retained pieces, and volume estimates |
| [Ninety109Endpoint](Kakeya/Ninety109Endpoint.lean) | Concrete overlap hypothesis, dyadic level bound, moment bound, and natural-log norm bound |
