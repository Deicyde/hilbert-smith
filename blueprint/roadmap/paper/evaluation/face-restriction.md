---
article_id: af_615384191925b26d3309b000
declaration: lemma
origin: background
---
# Face restriction

Let $Q$ be a box, and let $F$ be its face where the last arc factor is at its top endpoint. Let $p$ project $\partial Q\otimes P$ onto $F\otimes P$. Then $pd_{\partial Q}\iota=d_F$, and $p\,\varphi_{\partial Q}\,p^*-\varphi_{F}$ vanishes on every cochain of a cell not in $\partial F$, and also on every entry whose target is not in $\partial F$.

*Proof sketch.* $F$ is a subcomplex. In $\varphi_{\partial Q}$ the summand of the last arc, restricted to $F$, is $\varphi_F$: $\varphi_C([m]^*)=+[m]$, and inserting a factor of degree and dimension $0$ changes no Koszul sign. The other summands are restrictions to faces that meet $F$ only in $\partial F$.

## Sources
- New.
## Depends on
- [Block pair](../chain-models/blocks/block-pair.md)
## Proof depends on
- [Arc pair](../chain-models/blocks/arc-pair.md)
