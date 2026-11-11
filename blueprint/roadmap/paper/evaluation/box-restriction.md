---
article_id: af_918726e96ced045839d963f3
declaration: lemma
origin: background
---
# Box restriction

Let $Q=\bigotimes_jA_j\subseteq C(k)$ be a product of grid arcs $A_j\cong I_{m_j}$ with $m_j\le k-2$, and regard $Q\otimes P$ as the [block](../chain-models/blocks/block-pair.md) $I_{m_1}\otimes\dots\otimes I_{m_n}\otimes P$. Let $\iota$ and $p$ be the based inclusion and projection of $Q\otimes P$ in $D=C(k)\otimes P$. Then $p\,d_D\,\iota=d_{Q\otimes P}$ and $p\,\varphi_D\,p^*=\varphi_{Q\otimes P}$, where $\varphi_D$ is the structure of the [chain-model duality](../chain-models/grid/chain-model-duality.md).

*Proof sketch.*
1. Per factor, $\varphi^s(e_w^*)=\tfrac12([w]+[w+1])$ and $\varphi^s([w]^*)=\tfrac12(e_{w-1}+e_w)$ ([circle duality](../chain-models/grid/circle-duality.md)), so $p\varphi^sp^*=\varphi_I$ ([arc pair](../chain-models/blocks/arc-pair.md)): at an end vertex of the arc, $p$ removes the outside edge, and since $m_j\le k-2$ the outside edges are not arc edges. Likewise $pd\iota=d_I$.
2. Both $\varphi_D$ and $\varphi_{Q\otimes P}$ are iterated external products with the block signs $(-1)^{q(p+m)}$ ([chain-model duality](../chain-models/grid/chain-model-duality.md), item 1; [block pair](../chain-models/blocks/block-pair.md), item 3), and these signs depend only on the degrees and dimensions of the factors. The projections $p$ have degree $0$, so $p\varphi_Dp^*$ is the iterated product of the $p\varphi^sp^*$ and $\varphi_P$ with the same signs.

## Sources
- New. Replaces the union lemma of HS paper, Section 12.
## Depends on
- [Chain-model duality](../chain-models/grid/chain-model-duality.md)
- [Block pair](../chain-models/blocks/block-pair.md)
- [Chain model](../chain-models/grid/chain-model.md)
## Proof depends on
- [Circle duality](../chain-models/grid/circle-duality.md)
- [Arc pair](../chain-models/blocks/arc-pair.md)
