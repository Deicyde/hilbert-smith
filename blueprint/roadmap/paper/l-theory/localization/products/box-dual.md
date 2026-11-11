---
article_id: af_74d211a3e0f6e21de93fe8db
declaration: def
origin: background
statement: formalized
lean: HSP.boxPairing
---

# Duals of box products

For $N$ in $\operatorname{Kar}\mathcal B$ and $V$ in $C_\mathbb Z(\mathbb Q)$, let $\kappa_{N,V}:(N\boxtimes V)^*\to N^*\boxtimes V^*$ be the isomorphism of propagation $0$ that in position $n$ is the canonical isomorphism $(M^{\oplus d_n})^*\cong(M^*)^{\oplus d_n}$ of the [box product](box-product.md), whose components are the duals of the summand inclusions, followed by the idempotent $e^*$ on each summand when $N=(M,e)$ (so that it is a morphism of $\operatorname{Kar}C_\mathbb Z(\mathcal B)$). Then $(\boxtimes,\kappa)$ is a [duality pairing](duality-pairing.md) $\operatorname{Kar}\mathcal B\times C_\mathbb Z(\mathbb Q)\to\operatorname{Kar}C_\mathbb Z(\mathcal B)$.

*Proof sketch.* (Proof obligations.) (1) Naturality: the dual of a block matrix is the transposed block matrix of duals, and the $(i,i')$ entry $(g_{mn})_{ii'}f$ dualizes to $(g_{mn})_{ii'}f^*$, which is the $(i',i)$ entry of $f^*\boxtimes g^{\mathsf T}$. (2) $(\kappa_{N,V})^*=\kappa_{N^*,V^*}$: in position $n$, write $c:(\bigoplus_iX_i)^*\to\bigoplus_iX_i^*$ for the canonical isomorphism, with components $\iota_i^*$. Dualizing, $c\circ\pi_j^*$ has components $(\pi_j\iota_k)^*=\delta_{jk}$, so it is the inclusion $\iota'_j$ of $X_j^*$, and $\pi_j\circ c^*=(\iota'_j)^*$, which is the $j$-th component of the canonical isomorphism for the $X_i^*$.

## Sources

- New: the canonical isomorphism, needed because a strict duality need not commute with chosen biproducts on the nose.

## Depends on

- [Diagonal morphisms of $C_\mathbb Z(A)$](../../bounded/categories/bounded-diag.md)
- [Box product with a bounded vector space](box-product.md)
- [Duality pairings](duality-pairing.md)
- [The induced duality on $C_\mathbb Z(A)$](../../bounded/categories/bounded-duality.md)
- [Objects of the box product](bookkeeping/box-object.md)
- [Components of box products of maps](bookkeeping/box-components.md)
