---
declaration: lemma
origin: background
---
# Box restriction

Let $Q\subseteq C(k)$ be a grid box, with inclusion $\iota$ and projection $p$ of $Q\otimes P$ in $D=C(k)\otimes P$. Then $pd\iota=d_Q$ and $p\,\varphi_D\,p^*=\varphi_{Q\otimes P}$ exactly.

*Proof sketch.* Per factor, $\varphi^s(e_w^*)=\tfrac12([w]+[w+1])$ and $\varphi^s([w]^*)=\tfrac12(e_{w-1}+e_w)$, so $p\varphi^sp^*=\varphi_I$. At an endpoint, $p$ removes the outside edge. The maps $p$ have degree $0$, so the Koszul signs agree on both sides.

## Sources
- New. Replaces the union lemma of HS paper, Section 12.
## Depends on
- [Chain-model duality](../chain-models/chain-model-duality.md), [block pair](../chain-models/block-pair.md)
## Proof depends on
- [Circle duality](../chain-models/circle-duality.md), [arc pair](../chain-models/arc-pair.md)
