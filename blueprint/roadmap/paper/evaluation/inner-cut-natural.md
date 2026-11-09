---
declaration: lemma
origin: bridged
---
# Naturality of the inner cut

Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor carrying $\mathcal A_A,\mathcal A_B,\mathcal A_Y,\mathcal A_Z$ into $\mathcal A_{A'},\mathcal A_{B'},\mathcal A_{Y'},\mathcal A_{Z'}$, for inner-cut data on both sides. Then $\partial^{\rm in}_{A',B'}\bar F_*=(F|_{\mathcal A_Y})_*\partial^{\rm in}_{A,B}$. This applies to $\mathrm{pr}_*\circ U$ for $\mathrm{pr}:T\times S^n\to S^n$, with the sets of the [cut sets](cut-sets.md).

*Proof sketch.* $F$ induces functors on the three quotients that commute strictly with the identity-on-objects functors and with $e$. Then use [functoriality](../l-theory/D2.md) and the naturality of $\partial$ ([C5](../l-theory/C5.md), [C7](../l-theory/C7.md)). The application uses [support preservation](../categories/support-preservation.md) (a), (b).

## Sources
- HS paper, Sections 6 and 12.
## Depends on
- [Inner cut](inner-cut.md)
## Proof depends on
- [D2](../l-theory/D2.md), [C5](../l-theory/C5.md), [C7](../l-theory/C7.md), [support preservation](../categories/support-preservation.md)
