---
article_id: af_2d9f1a684d6a803f07cf3fa4
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.IsRetained
---
# Retained and discarded cells

Take [fixed local data](../local-data/control/fixed-local-data.md) with buffer radius $t$ and [torus test map](../chain-models/approximations/torus-test-map.md) $f_T$, and let $K_t=f_T^{-1}(\overline B(0,t))\subseteq\mathbb T^n$. A cell $c\otimes e_r$ of the [chain model](../chain-models/grid/model/chain-model.md) $D_i$, and its dual in $D_i^{N-*}$, is *retained* if the closed cube $|c|$ meets $K_t$, and *discarded* otherwise. Write $\mathrm{Ret}_i$ for the set of retained cells of $D_i$.

## Sources
- HS paper, Section 10 (far simplices). New: the cells are cubical, and the test is on the closed cube, not on the label.

## Depends on

- [The closed cube](../chain-models/grid/cubical/grid-cube-realization.md)
- [The cube of a chain-model cell](../chain-models/grid/model/chain-model-cube.md)
- [Grid cubes](../chain-models/grid/cubical/grid-cube.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
