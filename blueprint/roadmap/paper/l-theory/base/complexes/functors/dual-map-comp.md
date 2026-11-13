---
article_id: af_7799324778b47dc0214ae487
declaration: lemma
origin: background
statement: formalized
lean: HSP.dualCx.map_comp
proof: formalized
---

# Duals of chain maps reverse composition

For chain maps $f:C\to D$ and $g:D\to E$ and $n\in\mathbb Z$, the [duals](dual-map.md) satisfy $(gf)^{n-*}=f^{n-*}g^{n-*}$.

*Proof sketch.* In degree $r$ both sides are $(g_{n-r}f_{n-r})^*=f_{n-r}^*g_{n-r}^*$.

## Sources

- New: direct from the definitions.

## Depends on

- [Dual of a chain map](dual-map.md)
- [Dual complex](../dual-complex.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
