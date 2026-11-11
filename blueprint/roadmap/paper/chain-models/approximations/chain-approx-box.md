---
article_id: af_3f4f9ae19a4d2e186ede7b24
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainApproxBox
---

# Approximation boxes

Let $k\ge k_0$ (see the [mesh sequence](../grid/mesh-sequence.md)), put $h=4/k$, and let $L:\mathbb T^n\to\mathbb T^n$ be a map. For a cube $c$ of the [cubical torus grid](../grid/cubical-torus-grid.md) $C(k)$, the *approximation box* is
$$\Gamma_L(c)=\mathrm{Box}_k(N_h(L|c|)),$$
the [box hull](../grid/box-hull.md) of the closed $d_\infty$-neighbourhood $N_h(L|c|)$ of the image of the closed cube $|c|$. The box hull is taken in $C(k)$, which is defined since $k\ge k_0\ge 8$.

## Sources

- New: replaces simplicial approximation (HS paper, Section 9).

## Depends on

- [Box hull](../grid/box-hull.md), [mesh sequence](../grid/mesh-sequence.md), [cubical torus grid](../grid/cubical-torus-grid.md)
