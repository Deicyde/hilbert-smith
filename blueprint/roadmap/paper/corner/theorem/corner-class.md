---
article_id: af_fe5966c7d422963a286ca6fc
declaration: def
origin: bridged
---

# The corner class

Take the [standing data](../standing-data.md) and a [graph-type homotopy action](../actions/graph-type-action.md) on $(C,\phi)$. Let $(\operatorname{Ind}C,\Phi)$ be [the induced complex](induced-complex-poincare.md) and $E$ [the average](../actions/average.md), a [compatible homotopy idempotent](../actions/average-compatible-idempotent.md) on it. Choose:
- a splitting $(D,\iota,r)$ of $E$ in $\operatorname{Kar}\mathcal B_{\mathbf G,Z}(T\times S^n)$, with $D$ concentrated in $[0,N]$, which exists by [Splitting](homotopy-idempotent-splitting.md);
- $q=(q_i)$, acting at level $i$ as multiplication by the integer $q_i$; it has propagation $0$ and is invertible, central and self-adjoint.

The *corner class* is
$$\mathfrak d=\operatorname{cls}(D,q^{-1}r\Phi r^*)\in\mathbb L_N(\mathcal B_{\mathbf G,Z}(T\times S^n)),$$
where $(D,q^{-1}r\Phi r^*)$ is a strict Poincaré complex by [Corner duality](corner-duality.md).

This definition depends on the open statement [Idempotents split in the bounded homotopy category](kb-idempotent-splitting.md) ([Balmer and Schlichting 2001, Theorem 2.8](../../../../sources/paper/balmer-schlichting-2001.md) [U]), through [Splitting](homotopy-idempotent-splitting.md).

## Sources

- HS paper, Section 11.

## Depends on

- [Standing data](../standing-data.md)
- [Graph-type homotopy action](../actions/graph-type-action.md)
- [The induced complex](induced-complex-poincare.md)
- [The average](../actions/average.md)
- [The average is a compatible idempotent](../actions/average-compatible-idempotent.md)
- [Splitting a homotopy idempotent](homotopy-idempotent-splitting.md)
- [Corner duality](corner-duality.md)
- [Ultimate L-group and cls](../../l-theory/ultimate/groups/ultimate-l-group.md)
