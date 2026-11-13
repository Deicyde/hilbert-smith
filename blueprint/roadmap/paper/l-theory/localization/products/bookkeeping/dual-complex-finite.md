---
article_id: af_d6f7f4bbe6f13ad45add7422
declaration: lemma
origin: background
statement: formalized
lean: HSP.dualCx_finite
proof: formalized
---

# Dual complexes have finitely many nonzero chain objects

Let $C$ be a complex in a duality category with all but finitely many chain objects zero objects, and $m\in\mathbb Z$. Then all but finitely many chain objects of the [dual complex](../../../base/complexes/dual-complex.md) $C^{m-*}$ are zero objects.

*Proof sketch.* $(C^{m-*})_r=C_{m-r}^*$, and the dual of a zero object $X$ is a zero object, since $1_{X^*}=(1_X)^*=0^*=0$.

## Sources

- New: needed to form tensor products of dual complexes.

## Depends on

- [Dual complex](../../../base/complexes/dual-complex.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)
