---
article_id: af_d454f798f88c0f83dc7fc45a
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.cp2Inverse_comp_cp2Structure
---

# The CP^2 inverse inverts the structure

For the [cells of CP^2](../cp2/cp2-cells.md) and every degree $r$, the [inverse](../cp2/cp2-inverse.md) $b_P$ and the [structure](../cp2/cp2-structure.md) $\varphi_P$ are inverse to each other: $(\varphi_P)_{r,4-r}(b_P)_r=1$ on $P_r$ and $(b_P)_r(\varphi_P)_{r,4-r}=1$ on $P_{4-r}^*$.

*Proof sketch.* Both maps are all-ones matrices between $P_r$ and $P_{4-r}^*$, which have the same dimension, $1$ for $r\in\{0,2,4\}$ and $0$ otherwise.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Cells of CP^2](../cp2/cp2-cells.md)
- [The structure of CP^2](../cp2/cp2-structure.md)
- [The inverse of the structure of CP^2](../cp2/cp2-inverse.md)

## Proof depends on

- [The cellular chain complex of CP^2](../cp2/cp2-complex.md)

