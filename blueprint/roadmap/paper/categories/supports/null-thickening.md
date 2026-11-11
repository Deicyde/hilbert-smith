---
article_id: af_1ab3b2a9a1f822127a048b8d
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.exists_null_cthickening
---

# Null thickening radii

Let $M=(n_i,x_i)$ be an object of the [asymptotic category](../asymptotic/asymptotic-category.md), $S'\subset X$ and $Q$ a predicate on the indices of $M$. If for every $\varepsilon>0$ eventually all labels $x_i(k)$ with $Q(i,k)$ lie in the $\varepsilon$-thickening of $S'$, then there is a null sequence $r=(r_i)$ of nonnegative reals such that eventually all these labels lie in the closed $r_i$-thickening $\overline N_{r_i}(S')$.

*Proof sketch.* Take $r_i$ the largest distance (in $[0,\infty]$) from a label $x_i(k)$ with $Q(i,k)$ to $S'$. It tends to $0$, so it is eventually finite, and then it bounds each such distance.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Asymptotic category](../asymptotic/asymptotic-category.md)
