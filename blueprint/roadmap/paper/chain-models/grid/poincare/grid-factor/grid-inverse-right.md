---
article_id: af_3752c801cabacbe593f32260
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.gridStructureU_comp_gridDualMap
---

# The unsymmetrized grid structure inverts the grid duality map

For every $k$, $n$ and $r$, the [unsymmetrized grid structure](grid-structure-u.md) $\varphi^u_n$ and the [iterated grid duality map](grid-dual-map.md) $b=b^{(n)}$ satisfy $b_r(\varphi^u_n)_{r,n-r}=1$ on $C(k)_{n-r}^*$.

*Proof sketch.* Induction on $n$. On the unit complex both maps are the identity of $\mathbb Q$ in degree $0$. For $n+1$, [a product of duality maps after a product of structures](../../tensor/structure-products/str-prod-comp-dual-prod.md) is the dual tensor of the factorwise composites $b\varphi^u_n$ and $b\varphi$, which are identities by induction and by [circle duality](../../circle-duality.md) (1), and the [dual tensor of identities](../../tensor/structure-products/dual-tensor-hom-id.md) is the identity. The grid complex vanishes in negative degrees ([the grid complex vanishes in negative degrees](grid-dim-neg.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [The iterated grid duality map](grid-dual-map.md)
- [The unsymmetrized grid structure](grid-structure-u.md)
- [Cubical torus grid](../../cubical/cubical-torus-grid.md)
- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [A product of duality maps after a product of structures](../../tensor/structure-products/str-prod-comp-dual-prod.md)
- [Dual tensor of identities](../../tensor/structure-products/dual-tensor-hom-id.md)
- [Circle duality](../../circle-duality.md)
- [The grid complex vanishes in negative degrees](grid-dim-neg.md)
- [The identity of a dual complex as a map of degree zero](id-dual-deg0.md)
- [The unit complex](../../cubical/unit-complex.md)
- [The circle complex vanishes in negative degrees](../../cubical/circle-dim-neg.md)
- [Propagation](../../../../categories/asymptotic/propagation.md)
- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Augmentation of the circle complex](../../cubical/circle-aug.md)
- [The circle complex](../../cubical/circle-complex.md)
- [Fundamental chain of the circle complex](../../cubical/circle-fundamental.md)
- [Labels of the circle cells](../../cubical/circle-label.md)
- [The structure of the unit complex](../../model/unit-structure.md)
- [The circle inverse](../circle-data/circle-b.md)
- [The circle homotopy element](../circle-data/circle-h.md)
- [The dual circle homotopy](../circle-data/circle-k-dual.md)
- [The circle homotopy](../circle-data/circle-k.md)
- [The symmetric circle structure](../circle-data/circle-phi-sym.md)
- [The circle structure](../circle-data/circle-phi.md)
- [Dual tensor of graded maps of based complexes](../../tensor/based-dual-tensor-hom.md)
- [Product of duality maps in explicit bases](../../tensor/structure-products/based-dual-prod.md)
- [Product of structures in explicit bases](../../tensor/structure-products/based-str-prod.md)
- [Dual complex](../../../../l-theory/base/complexes/dual-complex.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [The involution T](../../../../l-theory/base/complexes/structure-involution.md)
