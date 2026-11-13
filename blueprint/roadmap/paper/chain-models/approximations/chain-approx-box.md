---
article_id: af_3f4f9ae19a4d2e186ede7b24
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainApproxBox
---

# Approximation boxes

Let $k\ge k_0$ (see the [mesh sequence](../grid/mesh-sequence.md)), put $h=4/k$, and let $L:\mathbb T^n\to\mathbb T^n$ be a map. For a cube $c$ of the [cubical torus grid](../grid/cubical/cubical-torus-grid.md) $C(k)$, the *approximation box* is
$$\Gamma_L(c)=\mathrm{Box}_k(N_h(L|c|)),$$
the [box hull](../grid/box-hull.md) of the closed $d_\infty$-neighbourhood $N_h(L|c|)$ of the image of the closed cube $|c|$. The box hull is taken in $C(k)$, which is defined since $k\ge k_0\ge 8$.

## Sources

- New: replaces simplicial approximation (HS paper, Section 9).

## Depends on

- [Mesh start](../mesh/mesh-start.md)
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [Grid boxes](../grid/grid-box.md)
- [The torus](../grid/torus.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [Modulus of the track family](modulus.md)
- [Box hull](../grid/box-hull.md)
- [The cube of a basis vector](../grid/cubical/grid-cell.md)
- [The closed cube](../grid/cubical/grid-cube-realization.md)
