---
article_id: af_8e00f9a96ef9196b6c4928d6
declaration: def
origin: background
---
# Pinch faces

Let $K=[-1/4,1/4]^n\subseteq\mathbb T^n$ and let $k_i$ be the [mesh sequence](../chain-models/grid/mesh-sequence.md). The [box hull](../chain-models/grid/box-hull.md) $\mathrm{Box}_{k_i}(K)=\bigotimes_jA_j$ is a product of grid arcs $A_j\cong I_{m_j}$. The *pinch faces* are the [blocks](../chain-models/blocks/block-pair.md) $Q^{(m)}_i$, $1\le m\le n$, defined as follows: $Q^{(1)}_i=I_{m_1}\otimes\dots\otimes I_{m_n}\otimes P$, and $Q^{(m+1)}_i$ is $Q^{(m)}_i$ with its arc factor in coordinate $n-m+1$ replaced by the point factor at the top vertex of that arc. So $Q^{(m)}_i$ has arc factors in coordinates $1,\dots,n-m+1$ and point factors after them. Each cell carries its torus position, and through it $Q^{(m)}_i$ is a based subcomplex of $D_i=C(k_i)\otimes P$.

## Sources
- New.
## Depends on
- [Box hull](../chain-models/grid/box-hull.md)
- [Block pair](../chain-models/blocks/block-pair.md)
- [Mesh sequence](../chain-models/grid/mesh-sequence.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
