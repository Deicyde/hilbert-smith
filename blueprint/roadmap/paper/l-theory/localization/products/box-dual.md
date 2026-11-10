---
article_id: af_74d211a3e0f6e21de93fe8db
declaration: def
origin: background
---

# Duals of box products

For $N$ in $\operatorname{Kar}\mathcal B$ and $V$ in $C_\mathbb Z(\mathbb Q)$, let $\kappa_{N,V}:(N\boxtimes V)^*\to N^*\boxtimes V^*$ be the isomorphism of propagation $0$ that in position $n$ is the canonical isomorphism $(M^{\oplus d_n})^*\cong(M^*)^{\oplus d_n}$ of the [box product](box-product.md). It is natural in both variables: $\kappa_{N,V}\circ(f\boxtimes g)^*=(f^*\boxtimes g^*)\circ\kappa_{N',V'}$ for $f:N\to N'$ and $g:V\to V'$.

*Proof sketch.* (Naturality.) The dual of a block matrix is the transposed block matrix of duals, and the $(i,i')$ entry $(g_{mn})_{ii'}f$ dualizes to $(g_{mn})_{ii'}f^*$, which is the $(i',i)$ entry of $f^*\boxtimes g^{\mathsf T}$.

## Sources

- New: the canonical isomorphism, needed because a strict duality need not commute with chosen biproducts on the nose.

## Depends on

- [Box product with a bounded vector space](box-product.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
