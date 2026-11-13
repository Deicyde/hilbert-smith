---
article_id: af_d019634c542cb492d6dd2ba1
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.groupApprox_carried
---
# Carried group approximations

For every $g\in G_i$, $a_g=a^T_g\otimes1_P$ where $a^T_g$ is a chain map of $C(k_i)$ carried by $\Gamma_{\widehat{r_i(g)}}$, the carrier of [approximation boxes](chain-approx-box.md) on the realization of $C(k_i)$ (as in [chain approximations exist](chain-approx-exists.md); [far cubes](far-cubes.md), [realized augmentation](../grid/realized-augmentation.md)), with $a^T_g|_{E(k_i)}=1$ and $\varepsilon a^T_g=\varepsilon$.

*Proof sketch.* For $g\ne0$ this is the choice made in [chain approximation](chain-approx.md). For $g=0$, $r_i(0)=0$, so $\widehat{r_i(0)}=\mathrm{id}$, and the identity is carried by $\Gamma_{\mathrm{id}}(c)=\mathrm{Box}_{k_i}(N_{h_i}(|c|))$, which contains $c$ by [box hull properties](../grid/box-hull-properties.md) (3).

## Sources
- New.
## Depends on

- [Mesh start](../mesh/mesh-start.md)
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [The cube of a basis vector](../grid/cubical/grid-cell.md)
- [Augmentation of the grid complex](../grid/cubical/grid-aug.md)
- [Completed representative](maps/completed-rep.md)
- [Group approximations](group-approx.md)
- [Tensoring with the identity of the cells of CP^2](tensor-one-p.md)
- [Approximation boxes](chain-approx-box.md)
- [Far cubes](far-cubes.md)
- [Carriers](../grid/carriers/acyclic-carriers.md)
- [Carried maps](../grid/carriers/carried-map.md)
- [Spans of cubes](../grid/cube-span.md)
- [Grid boxes](../grid/grid-box.md)
- [Mesh sequence](../grid/mesh-sequence.md)
- [Chain model](../grid/model/chain-model.md)
- [Realization of based complexes](../grid/realization.md)
- [Realized augmentation](../grid/realized-augmentation.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [Chain approximation](chain-approx.md)
- [Completed map](completed-map.md)
- [Box hull properties](../grid/box-hull-properties.md)
- [Representatives of the finite quotients](../../local-data/control/representative-map.md)
- [Chain approximations exist](chain-approx-exists.md)
