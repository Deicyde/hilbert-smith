---
article_id: af_b9a92d23a789594d5e0d1d8b
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.gridAug
---

# Augmentation of the grid complex

The *augmentation* of the [grid complex](cubical-torus-grid.md) is $\varepsilon^{\otimes n}:C(k)_0\to\mathbb Q$, the Kronecker product of the [augmentations](circle-aug.md) of the factors: by recursion on $n$, on the unique summand $C(k)_0\boxtimes S_{k,0}$ of $(C(k)\otimes S_k)_0$ it is the Kronecker product of $\varepsilon^{\otimes n}$ and $\varepsilon$. For $n=0$ it is the identity of $\mathbb 1_0=\mathbb Q$.

## Sources

- New: companion of the cubical torus grid.

## Depends on

- [Cubical torus grid](cubical-torus-grid.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [Augmentation of the circle complex](circle-aug.md)
- [The circle complex](circle-complex.md)
- [Block inclusions and projections](../tensor/blocks/block-maps.md)
- [Kronecker product of matrices](../../../l-theory/localization/products/bookkeeping/based-kron.md)
