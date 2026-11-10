---
article_id: af_040cc0cffa07acb48e022eb5
declaration: lemma
origin: bridged
---

# The exterior is closed

Let $n\ge1$, $R>0$, and let $T$ be a compact metric space with an isometric $C_p$-action, possibly empty. Then the [exterior](exterior.md) $Z_0$ is closed in $S^n$, and $Z=T\times Z_0$ is closed and $C_p$-invariant in $T\times S^n$.

*Proof sketch.*
1. The complement of $Z_0$ is the open ball $\{z\in\mathbb R^n:|z|<R\}$, which is open in $\mathbb R^n$ and hence in $S^n$.
2. $Z=T\times Z_0$ is a product of closed sets, so it is closed in the product topology, which the maximum metric induces.
3. $C_p$ moves only the first coordinate, so $c\cdot(t,z)=(c\cdot t,z)\in Z$ for $(t,z)\in Z$.

## Sources

- HS paper, Section 12.

## Depends on

- [The exterior](exterior.md)
- [The round sphere](round-sphere.md)
