---
article_id: af_a4ca4f7e2daa7765e556a47b
declaration: theorem
origin: bridged
---
# Block pairs in the asymptotic category

Let $(Q_i)_{i\ge1}$ be [blocks](block-pair.md) with the same factor types, so with the same $N_Q$, whose meshes are at most $h_i$, with $h_i\to0$. Let $X$ be a compact metric space with an isometric $C_p$-action, and let each cell $b$ of $Q_i$, and its dual, carry a label $\lambda_i(b)\in X$ such that, for every $c>0$,
$$\sup\{d_X(\lambda_ib,\lambda_ib'):d_\infty(x_b,x_{b'})\le ch_i\}\to0,$$
where $x_b$ is the centre of $b$ in the product of the factor realizations. Then $(j_i,\varphi_{Q_i},\varphi_{\partial Q_i})_i$ is a strict $N_Q$-dimensional symmetric Poincaré pair in the [asymptotic category](../../categories/asymptotic/asymptotic-category.md) $\mathcal A_{\mathbf 1}(X)$, the chain object of degree $r$ at level $i$ being the span of the cells of degree $r$ of $Q_i$ (or $\partial Q_i$) with the labels $\lambda_i$, enumerated as in the [cubical torus grid](../grid/cubical-torus-grid.md).

*Proof sketch.* By [block duality](block-duality.md) (3), the maps $\varphi_{Q_i},\varphi_{\partial Q_i},\theta_{Q_i},b_{Q_i},K_{Q_i,1},K_{Q_i,2}$ have $d_\infty$-propagation at most $h_i$; the differentials, the based inclusions $j_i$ and the based projections have $d_\infty$-propagation at most $h_i$ as well. By the label hypothesis their [propagation](../../categories/asymptotic/propagation.md) for the labels $\lambda_i$ tends to $0$, so the sequences are morphisms of $\mathcal A_{\mathbf 1}(X)$, and the identities of block duality (1) and (2) hold there exactly, levelwise. The argument of block duality (5) uses only these identities and lemmas valid in any duality category (the [split pair criterion](../../l-theory/base/pairs/split-pair-criterion.md), [mapping cones](../../l-theory/base/complexes/cone.md), [triangular equivalences](../../l-theory/base/complexes/triangular-equivalence.md) and [shifts](../../l-theory/base/complexes/shift-equivalence.md)), so it applies in $\mathcal A_{\mathbf 1}(X)$ with its [duality](../../categories/asymptotic/asymptotic-duality.md).

## Sources
- HS paper, Section 12 (relative duality, cylinders). New: the passage from one block to a sequence of labelled blocks.
## Depends on
- [Block pair](block-pair.md), [asymptotic category](../../categories/asymptotic/asymptotic-category.md), [duality on the asymptotic category](../../categories/asymptotic/asymptotic-duality.md), [propagation](../../categories/asymptotic/propagation.md), [strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md), [cubical torus grid](../grid/cubical-torus-grid.md)
## Proof depends on
- [Block duality](block-duality.md), [split pair criterion](../../l-theory/base/pairs/split-pair-criterion.md), [mapping cone](../../l-theory/base/complexes/cone.md), [twisted sum](../../l-theory/base/complexes/twisted-sum.md), [triangular map](../../l-theory/base/complexes/triangular-map.md), [triangular equivalences](../../l-theory/base/complexes/triangular-equivalence.md), [shifts of homotopy equivalences](../../l-theory/base/complexes/shift-equivalence.md)
