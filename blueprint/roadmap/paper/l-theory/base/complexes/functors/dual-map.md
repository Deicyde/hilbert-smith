---
article_id: af_5e36d1deb479e7f9763baff9
declaration: def
origin: background
statement: formalized
lean: HSP.dualCx.map
---

# Dual of a chain map

Let $f:C\to D$ be a chain map of complexes in a [duality category](../../categories/duality-category.md) and $n\in\mathbb Z$. Its *dual* is the chain map $f^{n-*}:D^{n-*}\to C^{n-*}$ between the [dual complexes](../dual-complex.md) with $(f^{n-*})_r=f_{n-r}^*$. It commutes with the differentials because $f$ does and the duality reverses composition, the signs $(-1)^r$ being the same on both sides.

## Sources

- New: direct from the definitions.

## Depends on

- [Dual complex](../dual-complex.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
