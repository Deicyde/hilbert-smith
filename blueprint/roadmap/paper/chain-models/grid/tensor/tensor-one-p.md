---
article_id: af_56473467da5fea682f5487d1
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.tensorOneP
---

# Tensoring with the identity of the cells of CP^2

Fix a local datum and an index $i$, and let $f$ be a map of degree $m$ of the [cubical grid](../cubical-torus-grid.md) $C(k_i)$, given by its components $f_r:C(k_i)_r\to C(k_i)_{r+m}$. Then $f\otimes1_P$ is the map of degree $m$ of the [chain model](../chain-model.md) $D_i=C(k_i)\otimes P$ given by the [tensor of graded maps](based-tensor-hom.md) of $f$ and the [identity of $P$ as a map of degree zero](id-deg0.md).

## Sources

- New: explicit bases for the chain models.

## Depends on

- [Chain model](../chain-model.md)
- [Tensor of graded maps of based complexes](based-tensor-hom.md)
- [The identity as a map of degree zero](id-deg0.md)
