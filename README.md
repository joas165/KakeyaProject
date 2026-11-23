# KakeyaProject

A Lean 4 formalization of dyadic incidence estimates for the Kakeya maximal function. The branch `feat/lemma48-conditional-endpoint` proves the fixed-parent application of Lemma 4.8 using globally indexed Vitali balls. It also proves a conditional logarithmic bound for tube multiplicity.

## Fixed-parent incidence estimate

Fix a dyadic level $q=2^m$. Each retained label $j$ specifies a parent tube and a ball index $\beta(j)$. The original retained piece satisfies $P_j\subseteq B_{\beta(j)}$. For the endpoint cover, the same label indexes the set $Q_j=G_{\mathrm{parent}(j)}\cap 3B_{\beta(j)}$, where $G_c$ is the greedy gain of parent $c$. The endpoint uses the incidence sets $I_j=\{\ell:T_\ell^\delta\cap Q_j\ne\varnothing\}$. The global ball index set $J_m$ is the image of all retained cover labels under $\beta$.

Fix a regular label $i$ and let $R_c$ be the regular labels with the same parent $c$ as $i$. For every $k$, the branch proves

$$
\left\{\ell\in I_i:\#\{j\in R_c:i\le j,\ \ell\in I_j\}\ge k\right\}
\subseteq
\left\{\ell:\#\{b\in J_m:T_\ell^\delta\cap T_c^\delta\cap 3B_b\ne\varnothing\}\ge k\right\}.
$$

A point of $T_\ell^\delta\cap Q_j$ witnesses the triple intersection at $b=\beta(j)$. Within $R_c$, distinct labels have distinct ball indices since the parent and ball index together determine the label.

| Lean declaration in `Kakeya.Ninety109.TubeFamily` | Result and hypotheses |
| --- | --- |
| `retainedPiece_subset_global_vitali_ball` | Identifies the global ball index of each endpoint cover piece and proves containment in its triple enlargement. |
| `R_c_orderedTail_subset_of_global_vitali_balls` | Proves the displayed inclusion for every $k$ from the tube-family construction. The proof establishes the ball hits and injectivity on $R_c$. |
| `parentTailApplication_of_ball_map` | For $k\ge k_0(n)$, bounds the left-hand cardinality by $C(n,A)qk^{1-n}$ via the global ball tail. This route assumes `GlobalVitaliDisjoint`: distinct original balls in $J_m$ are disjoint at each level. |
| `regular_tail_card_along_parent` | Proves the parent-class cardinality estimate directly using the balls selected for that parent and their established disjointness. |

## Conditional logarithmic endpoint

For $N\ge2$ tubes in dimension $n=d+2\ge3$, put $M=\sum_{\ell=1}^N\mathbf 1_{T_\ell^\delta}$ and $p=n/(n-1)$. Under the standing tube-family hypotheses and `OverlapApplication K`, `logarithmic_norm_bound` proves

$$
\lVert M\rVert_{L^p}\le C(n,A,K)(\log N)^{1/p}.
$$

At the relevant dyadic levels, `OverlapApplication K` supplies the ordered-tail estimate with the later label ranging over all regular labels. The theorem uses this hypothesis to bound the regular-piece count, combines it with the exceptional-piece estimate, and sums the resulting level-mass bounds. Deriving the total overlap needed by this argument from the $R_c$ estimates remains open in this branch.

## Source files

| Module | Contents |
| --- | --- |
| [Ninety110MultipleIncidences.lean](Kakeya/Ninety110MultipleIncidences.lean) | Angular concentration and the fixed-tube Vitali-ball tail |
| [Ninety110OrderedTails.lean](Kakeya/Ninety110OrderedTails.lean) | Ordered-tail counting identity and overlap estimates |
| [Ninety109RetainedCover.lean](Kakeya/Ninety109RetainedCover.lean) | Endpoint cover pieces, triple intersections, and greedy-union coverage |
| [Ninety109ExceptionalCount.lean](Kakeya/Ninety109ExceptionalCount.lean) | Exceptional-piece count at a dyadic level |
| [Ninety109Endpoint.lean](Kakeya/Ninety109Endpoint.lean) | Parent-class inclusion, global ball tail, level estimates, and logarithmic endpoint |

## Build

The project pins Lean 4.35.0. From the repository root, run

```sh
lake exe cache get
lake build Kakeya.Ninety109Endpoint
```

The declaration and axiom checks for these results are in [Audit.lean](Audit.lean).
