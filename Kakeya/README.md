# KakeyaProject

A Lean 4 formalization of dyadic estimates for the Kakeya maximal-function problem. This branch proves a conditional logarithmic endpoint for the project's unit-length Euclidean cylinders. **The logarithmic endpoint remains conditional. The branch also contains a direct full-`R` transfer of the proved fixed-tube geometric tail estimate; that transfer explicitly assumes forward ball hits and injectivity of ball labels.**

## Endpoint theorem

Let $n\ge 3$, $p=n/(n-1)$, and let $T_1^\delta,\ldots,T_N^\delta$ be unit-length cylinders of radius $\delta>0$ in $\mathbb R^n$, with $N\ge 2$. Their unit direction vectors satisfy $\lVert v_i-v_j\rVert\ge\delta$ for $i\ne j$. Fix $A>0$ with $\delta N^{1/(n-1)}\le A$. Write $M(x)=\sum_{i=1}^N\mathbf 1_{T_i^\delta}(x)$.

Under the chained bound below, `Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain` proves

$$
\lVert M\rVert_{L^p(\mathbb R^n)}
\le C(n,A,K)\,(\ln N)^{(n-1)/n}.
$$

The constant is uniform in $N$ and $\delta$ for fixed $n,A,K$. In Lean the dimension is written as $n=d+2$, with $d\ge1$.

## Lemma 4.8 and the full-`R` ordered tail

Fix a multiplicity level $q=2^m$, with $q\ge8$ and radius
$\rho=Cq^{-1/(n-1)}$. Let $R$ be the set of regular retained labels and
let $I_i$ consist of the indices of original tubes meeting the retained
piece $P_i$. For a fixed regular label $i$, define

$$
D_i(\ell)=\{j\in R:i\le j,\ \ell\in I_j\},\qquad
A_{i,k}=\{\ell\in I_i:|D_i(\ell)|\ge k\}.
$$

The count defining $D_i$ uses the entire set $R$.

Lemma 4.8 is formalized in `Ninety110MultipleIncidences`. For a fixed
unit tube $T_t^\delta$, a finite family of pairwise disjoint open
radius-$\rho$ balls indexed by $J$, and $k\ge k_0(n)$, the theorem
`fixed_tube_vitali_ball_tail` bounds the number of original tubes
meeting at least $k$ of their triple-radius enlargements along
$T_t^\delta$. Set

$$
H_{t,J}(\ell)=\big\{b\in J:
T_\ell^\delta\cap T_t^\delta\cap 3B_b\ne\varnothing\big\}.
$$

Its dyadic conclusion is

$$
\left|\{\ell:|H_{t,J}(\ell)|\ge k\}\right|
\le C_n(k\rho)^{1-n}
\lesssim_{n,C}qk^{1-n}.
$$

The theorem `ordered_tail_card_of_forward_ball_hits` in
`Ninety110OrderedTails` transfers this result **directly for the full
set $R$**. It uses a ball assignment $b:R\to J$ satisfying:

- `hforward`: for every $\ell\in I_i$ and $j\in D_i(\ell)$, the assigned
  $b(j)$ lies in $J$, and $T_\ell^\delta\cap T_t^\delta\cap3B_{b(j)}$
  is nonempty;
- `hinj`: the ball assignment is injective on $R$.

These assumptions yield $|D_i(\ell)|\le |H_{t,J}(\ell)|$ for
$\ell\in I_i$. The Lean proof applies `Finset.card_le_card_of_injOn`
to the assignment and then the already proved geometric estimate:

$$
\boxed{
|A_{i,k}|
\le\left|\{\ell:|H_{t,J}(\ell)|\ge k\}\right|
\lesssim_{n,C}qk^{1-n}.
}
$$

`orderedTail_subset_geometricHits` and
`orderedTail_card_le_geometricHits` express the finite-set comparison
with independent label types for retained pieces and balls.
`ordered_tail_card_of_fixed_tube_vitali_ball_tail` gives the same
transfer from an abstract cardinality comparison. No splitting of $R$
is used in the full-`R` theorem.

**What remains:** `hforward` and `hinj` are explicit hypotheses of
`ordered_tail_card_of_forward_ball_hits`; they have not been derived
here for the complete concrete retained-piece construction. The
previous `regular_tail_card_along_parent` theorem uses its own
fixed-parent geometry, but that fact alone does not discharge these
full-`R` hypotheses. A successful compilation establishes the Lean
implication with these premises, not an unconditional global incidence
bound.

## Lemma 4.9 and the conditional endpoint

`orderedTail_eq_inter_selection2` proves the finite-set identity
$A_{i,k}=I_i\cap\{\ell:|D_i(\ell)|\ge k\}$, and
`orderedTail_card_le_selection2` proves its cardinal inequality.
The ordered overlap identity is

$$
\sum_{j\in R:\ i<j}|I_i\cap I_j|
=\sum_{k=2}^{|R|}|A_{i,k}|.
$$

The definitions `OrderedTailChainApplication`, `regularTailChain` and
`TubeFamily.TailChainApplication K` retain the endpoint's single
conditional chain at every relevant dyadic level. The first inequality
of that chain is already proved by set inclusion. Its global numerical
tail estimate remains a premise of
`TubeFamily.logarithmic_norm_bound_of_tail_chain`. The direct full-`R`
geometric bridge has not yet been used to discharge that premise for
the concrete family.

For $2\le k<k_0(n)$, the count is bounded by $|I_i|$. For larger
thresholds, the assumed ordered-tail estimate yields an overlap
coefficient bounded by $k_0(n)+K\sum_{k\ge1} k^{1-n}$.

## From overlap to the endpoint

Each regular piece contains a point of $F_m$, so $q\le |I_i|$. Counting first and second moments of the incidence degrees, then applying Cauchy–Schwarz, gives $q|R|\le (1+2D)N$. For the exceptional pieces, which satisfy $2|I_i|>N$, the formalization applies the proved fixed-parent estimate separately within each parent class. Adding the greedy parent count gives an $O_{n,A,K}(N/q)$ bound for the complete retained family.

The same triple-radius pieces cover the greedy gains and enter the piece-volume estimate. Their count and mass capture give a uniform bound on $q^p|F_m|$. The remaining small levels use the finite-volume estimate. Summing the dyadic levels gives the logarithmic moment bound and taking the $p$th root gives the endpoint above.

## Build and check

From a checkout of this branch, use the pinned Lean 4.35.0 toolchain. To fetch the mathlib cache and build the endpoint module, run

```sh
lake exe cache get
lake build Kakeya.Ninety109Endpoint
```

Run `lake build Kakeya.Ninety110OrderedTails` to check the full-`R` transfer, and `lake build` for the whole project. Run `lake env lean Audit.lean` to check the declarations listed in the axiom audit. For a focused inspection of the transfer and endpoint signatures, use:

```lean
import Kakeya.Ninety110OrderedTails
import Kakeya.Ninety109Endpoint

#check Kakeya.Ninety109.ordered_tail_card_of_forward_ball_hits
#print axioms Kakeya.Ninety109.ordered_tail_card_of_forward_ball_hits
#check Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_tail_chain
```

The standard proof dependencies are `propext`, `Classical.choice`, and `Quot.sound`; verify the actual output with the command above. The explicit hypothesis `hchain : f.TailChainApplication K` is a theorem parameter, not a Lean axiom. Likewise, the `hforward` and `hinj` hypotheses are explicit theorem parameters, not global axioms.

## Source files

| Module | Contents |
| --- | --- |
| [Ninety110MultipleIncidences](Kakeya/Ninety110MultipleIncidences.lean) | Lemma 4.8, angular concentration and the geometric tail bound |
| [Ninety110OrderedTails](Kakeya/Ninety110OrderedTails.lean) | Full-`R` forward-ball-hit transfer, ordered-tail identity, conditional chain, Lemma 4.9, and overlap |
| [Ninety109FixedParentOverlap](Kakeya/Ninety109FixedParentOverlap.lean) | Fixed-parent geometry, the ordered overlap inequality, and the incidence second-moment estimate |
| [Ninety109RegularPieceCount](Kakeya/Ninety109RegularPieceCount.lean) | Regular-piece count from the overlap application |
| [Ninety109RetainedCover](Kakeya/Ninety109RetainedCover.lean) | Triple-radius retained pieces and coverage of the greedy gains |
| [Ninety109ExceptionalCount](Kakeya/Ninety109ExceptionalCount.lean) | Exceptional-piece count at each relevant level |
| [Ninety109TubeFamily](Kakeya/Ninety109TubeFamily.lean) | Euclidean tube family, canonical retained pieces, and volume estimates |
| [Ninety109Endpoint](Kakeya/Ninety109Endpoint.lean) | Chained-tail endpoint hypothesis, ordered-tail application, dyadic level bound, moment bound, and natural-log norm bound |
