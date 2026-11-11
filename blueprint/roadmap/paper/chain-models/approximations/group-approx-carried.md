---
article_id: af_d019634c542cb492d6dd2ba1
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.groupApprox_carried
---
# Carried group approximations

For every $g\in G_i$, $a_g=a^T_g\otimes1_P$ where $a^T_g$ is a chain map of $C(k_i)$ carried by $\Gamma_{\widehat{r_i(g)}}$ of [chain approximations exist](chain-approx-exists.md), [far cubes](far-cubes.md), [approximation boxes](chain-approx-box.md), [realized augmentation](../grid/realized-augmentation.md), with $a^T_g|_{E(k_i)}=1$ and $\varepsilon a^T_g=\varepsilon$.

*Proof sketch.* For $g\ne0$ this is the choice made in [chain approximation](chain-approx.md). For $g=0$, $r_i(0)=0$, so $\widehat{r_i(0)}=\mathrm{id}$, and the identity is carried by $\Gamma_{\mathrm{id}}(c)=\mathrm{Box}_{k_i}(N_{h_i}(|c|))$, which contains $c$ by [box hull properties](../grid/box-hull-properties.md) (3).

## Sources
- New.
## Depends on
- [Mesh start](../mesh/mesh-start.md)
- [Cubical torus grid](../grid/cubical/cubical-torus-grid.md)
- [The cube of a basis vector](../grid/cubical/grid-cell.md)
- [Augmentation of the grid complex](../grid/cubical/grid-aug.md)
- [Completed representative](maps/completed-rep.md)
- [Group approximations](group-approx.md), [chain approximations exist](chain-approx-exists.md), [tensoring with the identity of the cells of CP^2](tensor-one-p.md)
## Proof depends on
- [Chain approximation](chain-approx.md), [completed map](completed-map.md), [box hull properties](../grid/box-hull-properties.md), [representatives](../../local-data/control/representative-map.md)
