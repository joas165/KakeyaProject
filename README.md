# KakeyaProject

A Lean 4 formalization of dyadic estimates for the Kakeya maximal-function problem. This branch proves a conditional logarithmic endpoint for the project's unit-length Euclidean cylinders. **The build is complete. The endpoint theorem is conditional on the stated ordered-tail chain. Its first inequality is proved by set inclusion; its second inequality is the sole unproved incidence estimate.**

## Endpoint theorem

Let $n\ge 3$, $p=n/(n-1)$, and let $T_1^\delta,\ldots,T_N^\delta$ be unit-length cylinders of radius $\delta>0$ in $\mathbb R^n$, with $N\ge 2$. Their unit direction vectors satisfy $\lVert v_i-v_j\rVert\ge\delta$ for $i\ne j$. Fix $A>0$ with $\delta N^{1/(n-1)}\le A$. Write $M(x)=\sum_{i=1}^N\mathbf 1_{T_i^\delta}(x)$.

Under the chained bound below, `Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain` proves

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

Lemma 4.8 fixes a unit tube $T_i^\delta$ and a family of disjoint radius-$\rho$ balls indexed by $J$. For an original tube to belong to the geometric set, at least $k$ distinct enlarged balls must meet $T_\ell^\delta\cap T_i^\delta$. For $k\ge k_0(n)$, Lean proves the unoriented angle bound $C_n\delta/(k\rho)$, the cardinal bound $C'_n(k\rho)^{1-n}$, and its dyadic form for $\rho=Aq^{-1/(n-1)}$.

For a fixed tube, `fixed_tube_vitali_ball_tail` gives the dyadic estimate on its enlarged balls. The forward implication `triple_hit_of_coverPiece_incidence` transfers each retained-piece hit to the same ball. The resulting `fixed_tube_vitali_piece_tail` is used by `TubeFamily.regular_tail_card_along_parent` for ordered regular labels along that parent.

The application on pages 15–16 uses the ordered incidence sets
$$
A_{i,k}=\{\ell\in I_i:\ \#\{j\in R:i\le j,\ \ell\in I_j\}\ge k\}.
$$

The endpoint theorem assumes the following chain, uniformly for every regular label $i\in R$, every $k\ge k_0(n)$, and every relevant level $q\ge8$ with radius at most one:
$$
\boxed{
\begin{aligned}
&\left|\left\{\ell\in I_i:\#\{j\in R:i\le j,\ \ell\in I_j\}\ge k\right\}\right|\\
&\qquad\le
\left|\{\ell\in\{1,\ldots,N\}:|S_i(\ell)|\ge k\}\right|\\
&\qquad\le Kqk^{1-n}.
\end{aligned}
}
$$
Here $K$ is uniform in the dyadic level, and the labels $j$ range over all of $R$, including labels from different parents. The exponent is $1-n=-(d+1)$.

For every fixed label $i$, define **the same later-piece incidences**
$$
S_i(\ell)=\{j\in R:i\le j,\ \ell\in I_j\}.
$$
Each label $j$ refers to its corresponding retained piece and ball. The counting
set in Selection 2 is
$$
G_{i,k}=\{\ell\in\{1,\ldots,N\}:|S_i(\ell)|\ge k\}.
$$
By definition,
$$
A_{i,k}=I_i\cap G_{i,k}\subseteq G_{i,k},
$$
so **Selection 2 directly implies Selection 1**:
$$
|A_{i,k}|\le |G_{i,k}|\le Kqk^{1-n}.
$$
The inclusion is unconditional. The fixed-parent estimate counts hits only from
labels with a common parent. The set $G_{i,k}$ also counts hits across different
parents, and membership in $G_{i,k}$ alone gives no intersection with $P_i$.

In `Ninety110OrderedTails`, `orderedTail_eq_inter_selection2` now proves the
identity unconditionally, `orderedTail_subset_laterIncidences` proves the subset inclusion,
and `orderedTail_card_le_selection2` proves the first inequality of the ordered-tail chain.
`orderedTailApplication_of_selection2` combines the inequality with the
Selection 2 estimate. At the concrete level,
`regularApplication_of_selection2` and
`TubeFamily.overlapApplication_of_selection2` connect this implication to the
existing incidence counting argument.

`OrderedTailChainApplication` expresses precisely the two inequalities in the
boxed hypothesis. The concrete `regularTailChain` and
`TubeFamily.TailChainApplication K` specialize it to the retained regular
pieces at every relevant dyadic level. The main endpoint theorem
`TubeFamily.logarithmic_norm_bound_of_tail_chain` takes a single assumption
`hchain : f.TailChainApplication K`, then uses
`regularApplication_of_tail_chain` and
`TubeFamily.overlapApplication_of_tail_chain` to supply the existing counting
argument. The previously established `orderedTail_card_le_selection2` proves
the first inequality outright from the subset inclusion. The second inequality of the
ordered-tail chain is conditional: its global geometric estimate has not been
established in these files.

The earlier `TubeFamily.logarithmic_norm_bound_of_selection2` theorem remains
available and has the same conclusion from the second inequality alone.

For $2\le k<k_0(n)$ the proof uses $A_{i,k}\subseteq I_i$. Lemma 4.9 gives the exact identity
$$
\sum_{j\in R:\ i<j}|I_i\cap I_j|
=\sum_{k=2}^{|R|}|A_{i,k}|.
$$
Summing the tail bound gives the ordered overlap inequality with coefficient $D=k_0(n)+K\sum_{k\ge1} k^{1-n}$.

## From overlap to the endpoint

Each regular piece contains a point of $F_m$, so $q\le |I_i|$. Counting first and second moments of the incidence degrees, then applying Cauchy–Schwarz, gives $q|R|\le (1+2D)N$. For the exceptional pieces, which satisfy $2|I_i|>N$, the formalization applies the proved fixed-parent estimate separately within each parent class. Adding the greedy parent count gives an $O_{n,A,K}(N/q)$ bound for the complete retained family.

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

#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
```

The standard proof dependencies are `propext`, `Classical.choice`, and `Quot.sound`; verify the actual output with the command above. The explicit hypothesis `hchain : f.TailChainApplication K` is a theorem parameter, not a Lean axiom.

## Source files

| Module | Contents |
| --- | --- |
| [Ninety110MultipleIncidences](Kakeya/Ninety110MultipleIncidences.lean) | Lemma 4.8, angular concentration and the geometric tail bound |
| [Ninety110OrderedTails](Kakeya/Ninety110OrderedTails.lean) | Ordered-tail identity and subset proof, chained conditional estimate, fixed-tube tail transfer, Lemma 4.9, and ordered overlap |
| [Ninety109FixedParentOverlap](Kakeya/Ninety109FixedParentOverlap.lean) | Fixed-parent geometry, the ordered overlap inequality, and the incidence second-moment estimate |
| [Ninety109RegularPieceCount](Kakeya/Ninety109RegularPieceCount.lean) | Regular-piece count from the overlap application |
| [Ninety109RetainedCover](Kakeya/Ninety109RetainedCover.lean) | Triple-radius retained pieces and coverage of the greedy gains |
| [Ninety109ExceptionalCount](Kakeya/Ninety109ExceptionalCount.lean) | Exceptional-piece count at each relevant level |
| [Ninety109TubeFamily](Kakeya/Ninety109TubeFamily.lean) | Euclidean tube family, canonical retained pieces, and volume estimates |
| [Ninety109Endpoint](Kakeya/Ninety109Endpoint.lean) | Chained-tail endpoint hypothesis, ordered-tail application, dyadic level bound, moment bound, and natural-log norm bound |
