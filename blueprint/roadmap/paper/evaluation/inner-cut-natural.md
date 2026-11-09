---
article_id: af_40d450699c590dde7eae351f
declaration: lemma
origin: bridged
---
# Naturality of the inner cut

Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor carrying $\mathcal A_A,\mathcal A_B,\mathcal A_Y,\mathcal A_Z$ into $\mathcal A_{A'},\mathcal A_{B'},\mathcal A_{Y'},\mathcal A_{Z'}$, for inner-cut data on both sides. Then $\partial^{\rm in}_{A',B'}\bar F_*=(F|_{\mathcal A_Y})_*\partial^{\rm in}_{A,B}$. This applies to $\mathrm{pr}_*\circ U$ for $\mathrm{pr}:T\times S^n\to S^n$, with the sets of the [cut sets](cut-sets.md).

*Proof sketch.* $F$ induces functors on the three quotients that commute strictly with the identity-on-objects functors and with $e$. Then use [functoriality](../l-theory/ultimate/groups/induced-map-comp.md) and the naturality of $\partial$ ([naturality of the boundary](../l-theory/localization/sequence/boundary-naturality.md), [naturality of the transition](../l-theory/localization/line/transition-naturality.md)). The application uses that [pushforward](../categories/functors/push-support.md) and [forgetting the group](../categories/functors/forget-group-support.md) preserve supports.

## Sources
- HS paper, Sections 6 and 12.
## Depends on
- [Inner cut](inner-cut.md)
## Proof depends on
- [functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md), [naturality of the boundary](../l-theory/localization/sequence/boundary-naturality.md), [naturality of the transition](../l-theory/localization/line/transition-naturality.md), [pushforward preserves support](../categories/functors/push-support.md), [forgetting the group preserves support](../categories/functors/forget-group-support.md)
