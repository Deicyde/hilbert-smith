---
article_id: af_a5df2995f874bf59f0daaf41
declaration: lemma
origin: bridged
---

# Trivializing closed cover

There are $s\ge1$ and closed invariant $T_1,\dots,T_s$ covering $X$, each with a continuous equivariant map $c_a:T_a\to C_p$.

*Proof sketch.*
1. If $X=\varnothing$, take $s=1$ and $T_1=\varnothing$.
2. Otherwise, for each $x$ put $\eta(x)=\min_{g\ne0}d(x,gx)$, which is positive by freeness, and $r=\eta(x)/4$.
3. The balls $\bar B(gx,r)$ are pairwise at distance at least $\eta/2$. Their union $K_x$ is closed and invariant, and $c(y)=g$ on $\bar B(gx,r)$ is continuous and equivariant.
4. The open balls $B(x,r)$ cover $X$; take a finite subcover.

## Sources

- HS paper, Section 4.
- New: an explicit saturated-ball cover.

## Depends on
