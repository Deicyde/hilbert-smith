---
article_id: af_ad88302a24fadd9f18c33c4b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.gridDualMap_comp_gridStructureU
---

# The grid duality map inverts the unsymmetrized grid structure

For every $k$, $n$ and $r$, the iterated duality map $b=b\otimes\cdots\otimes b$ of [chain-model duality](../chain-model-duality.md) and the [unsymmetrized grid structure](grid-structure-u.md) $\varphi^u_n$ satisfy $(\varphi^u_n)_{r,n-r}b_r=1$ on $C(k)_r$.

*Proof sketch.* Induction on $n$. On the unit complex both maps are the identity of $\mathbb Q$ in degree $0$. For $n+1$, [a product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md) is the tensor of the factorwise composites $\varphi^u_nb$ and $\varphi b$, which are identities by induction and by [circle duality](../circle-duality.md) (1), and the [tensor of identities](../tensor/tensor-hom-id.md) is the identity. The grid complex vanishes in negative degrees ([the grid complex vanishes in negative degrees](grid-dim-neg.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [The unsymmetrized grid structure](grid-structure-u.md)

## Proof depends on

- [A product of structures after a product of duality maps](../tensor/structure-products/dual-prod-comp-str-prod.md)
- [Tensor of identities](../tensor/tensor-hom-id.md)
- [Circle duality](../circle-duality.md)
- [The grid complex vanishes in negative degrees](grid-dim-neg.md)
