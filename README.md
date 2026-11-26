# KakeyaProject

This project formalizes dyadic incidence estimates for the Kakeya maximal function in Lean 4. The logarithmic endpoint for tube multiplicity follows from the **second equality on page 16** of the manuscript. The first equality is a proved counting identity. So the proof is conditional only on equation (8) of the manuscript.

## The two equalities

Fix a dyadic level $q=2^m$. Let $R$ be the ordered set of regular retained labels, $I_i$ the original tube indices incident to the cover piece of label $i$, and $R_c$ the labels whose parent is $c$. The ordered tail counts later labels throughout $R$ and includes $i$ itself:

$$
E_{i,k}=\{\ell\in I_i : \#\{j\in R : i\le j,\ \ell\in I_j\}\ge k\}.
$$

**First equality (proved).** Each later occurrence of a tube index contributes once to the sum over thresholds. The theorem `global_overlap_eq_sum_tails` gives

$$
\sum_{\substack{i,j\in R\\i<j}} |I_i\cap I_j|
=\sum_{k=2}^{|R|}\sum_{i\in R}|E_{i,k}|.
$$

**Second equality (assumed).** At each level with $q\ge8$ and retained ball radius at most $1$, the hypothesis `TubeFamily.SecondEqualityApplication` requires

$$
\sum_{k=2}^{|R|}\sum_{i\in R}|E_{i,k}|
=\sum_{c\in B}\sum_{\substack{r,s\in R_c\\r<s}} |I_r\cap I_s|.
$$

The right-hand sum counts each unordered pair with the same parent once. This equality is the open hypothesis of the branch theorem.

## From the equality to the endpoint

Restricting the later labels to the parent of $i$ gives a comparison set contained in $E_{i,k}$. The sum of the comparison cardinalities equals the same-parent pair sum. Under the second equality, the total of the nonnegative cardinality differences is zero. Consequently each difference is zero, and the proved fixed-parent angular estimate applies to $|E_{i,k}|$ at every sufficiently large threshold.

The endpoint proof uses this estimate to count the regular pieces, adds the exceptional-piece budget, and sums the dyadic mass bounds. For a tube family with parameter $A$, dimension $n=d+2\ge3$, $N\ge2$, and $p=n/(n-1)$, the conclusion is

$$
\left\|\sum_{\ell=1}^{N}\mathbf 1_{T_\ell^\delta}\right\|_{L^p}
\le C(n,A)(\log N)^{1/p}.
$$

| Declaration in `Kakeya.Ninety109` | Source |
| --- | --- |
| `global_overlap_eq_sum_tails` | [Ninety118FirstEquality.lean](Kakeya/Ninety118FirstEquality.lean) |
| `SecondOverlapEquality`, `global_tail_card_of_secondEquality` | [Ninety118SecondEquality.lean](Kakeya/Ninety118SecondEquality.lean) |
| `TubeFamily.regular_tail_card_along_parent` | [Ninety109Endpoint.lean](Kakeya/Ninety109Endpoint.lean) |
| `TubeFamily.SecondEqualityApplication`, `TubeFamily.logarithmic_norm_bound_of_secondEquality` | [Ninety118SecondEquality.lean](Kakeya/Ninety118SecondEquality.lean) |

## Build and audit

The project pins Lean 4.35.0. Run these commands from the repository root.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The [audit](Audit.lean) prints the second-equality hypothesis, the endpoint signature, and the declarations' axiom dependencies. The endpoint depends on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The second equality appears as a theorem parameter.
