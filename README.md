# KakeyaProject

Lean 4 formalization of the dyadic Kakeya maximal-function argument using greedy tube selection, Vitali balls, retained pieces, and incidence counting.

## Conditional endpoint

For unit-length tubes \(T_1^\delta,\ldots,T_N^\delta\) in \(\mathbb R^n\), \(n=d+2\ge3\), let
\[
M(x)=\sum_{\ell=1}^{N}\mathbf1_{T_\ell^\delta}(x),
\qquad p=\frac{n}{n-1}.
\]
The target theorem, `TubeFamily.logarithmic_norm_bound_of_parent_subset` in `Kakeya/Ninety109Endpoint.lean`, gives
\[
\|M\|_{L^p}\le C(n,A)(\log N)^{1/p}
\]
under the two assumptions below, together with the standing `TubeFamily` conditions and \(N\ge2\).

At dyadic level \(q=2^m\), let \(R=\bigsqcup_{c\in B}R_c\) be the regular retained-piece labels, grouped by greedy parent tube. Define
\[
I_i=\{\ell:T_\ell^\delta\cap P_i\ne\varnothing\},\qquad
A_{i,k}=\left\{\ell\in I_i:\#\{j\in R:i\le j,\ \ell\in I_j\}\ge k\right\}.
\]
The index \(j\) ranges over **all** of \(R\), as in Lemma 4.9.

Let \(J\) be the **global family of selected Vitali-ball labels**, the union of the selected ball sets over the greedy parent tubes \(c\in B\). For the fixed tube \(T_{\operatorname{parent}(i)}^\delta\), put
\[
H_{i,k}=\left\{\ell:\#\left\{b\in J:
T_\ell^\delta\cap T_{\operatorname{parent}(i)}^\delta\cap3B_b\ne\varnothing
\right\}\ge k\right\}.
\]
The endpoint currently requires:

1. **Global ball disjointness:** `TubeFamily.GlobalVitaliDisjoint` — the original balls \(B_b\), \(b\in J\), are pairwise disjoint at each level.
2. **Incidence-transfer inclusion:** `TubeFamily.ParentSubsetApplication` — \(A_{i,k}\subseteq H_{i,k}\) for the relevant levels \(q\ge8\), radii \(\rho\le1\), and thresholds \(k\ge k_0(n)\).

Given the first assumption, the formalized fixed-tube Lemma 4.8 estimates
\[
|H_{i,k}|\lesssim_{n,A}qk^{1-n}.
\]
The second assumption transfers this estimate to \(A_{i,k}\). Lemma 4.9's existing ordered-tail double-counting identity then feeds the regular-piece count, exceptional-piece estimate, retained-cover bounds, and dyadic summation. **Neither assumption has been discharged in this branch.** The endpoint is not unconditional.

## Code and validation

| File | Role |
| --- | --- |
| `Kakeya/Ninety110MultipleIncidences.lean` | Angular packing and fixed-tube Lemma 4.8 |
| `Kakeya/Ninety110OrderedTails.lean` | Lemma 4.9 ordered-tail counting |
| `Kakeya/Ninety109Endpoint.lean` | Global ball tail, conditional inclusion, endpoint |
| `Kakeya/Ninety109RegularPieceCount.lean` | Regular-piece count |
| `Kakeya/Ninety109ExceptionalCount.lean` | Exceptional-piece estimate |

The current `Ninety109Endpoint.lean` has **not passed the local Lean 4.35 build**; recent logs report elaboration and type-mismatch errors. Do not treat the endpoint as compiler-verified until those are resolved.

```sh
lake exe cache get
lake build Kakeya.Ninety109Endpoint
```

For the endpoint axiom audit, after a successful build:

```lean
import Kakeya.Ninety109Endpoint
#print axioms Kakeya.Ninety109.TubeFamily.logarithmic_norm_bound_of_parent_subset
```
