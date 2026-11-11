---
article_id: af_3752c801cabacbe593f32260
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.gridStructureU_comp_gridDualMap
---

# The unsymmetrized grid structure inverts the grid duality map

For every $k$, $n$ and $r$, the [unsymmetrized grid structure](grid-structure-u.md) $\varphi^u_n$ and the iterated duality map $b=b\otimes\cdots\otimes b$ of [chain-model duality](../../chain-model-duality.md) satisfy $b_r(\varphi^u_n)_{r,n-r}=1$ on $C(k)_{n-r}^*$.

*Proof sketch.* Induction on $n$. On the unit complex both maps are the identity of $\mathbb Q$ in degree $0$. For $n+1$, [a product of duality maps after a product of structures](../../tensor/structure-products/str-prod-comp-dual-prod.md) is the dual tensor of the factorwise composites $b\varphi^u_n$ and $b\varphi$, which are identities by induction and by [circle duality](../../circle-duality.md) (1), and the [dual tensor of identities](../../tensor/structure-products/dual-tensor-hom-id.md) is the identity. The grid complex vanishes in negative degrees ([the grid complex vanishes in negative degrees](grid-dim-neg.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [The iterated grid duality map](grid-dual-map.md)
- [The unsymmetrized grid structure](grid-structure-u.md)
- [Chain-model duality](../../chain-model-duality.md)

## Proof depends on

- [A product of duality maps after a product of structures](../../tensor/structure-products/str-prod-comp-dual-prod.md)
- [Dual tensor of identities](../../tensor/structure-products/dual-tensor-hom-id.md)
- [Circle duality](../../circle-duality.md)
- [The grid complex vanishes in negative degrees](grid-dim-neg.md)
- [The identity of a dual complex as a map of degree zero](id-dual-deg0.md)
