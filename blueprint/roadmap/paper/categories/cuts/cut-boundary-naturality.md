---
article_id: af_25df0020e6965002239bec6f
declaration: lemma
origin: bridged
---

# Naturality of the cut boundary

Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor carrying $\mathcal A_A,\mathcal A_B,\mathcal A_Z$ into $\mathcal A_{A'},\mathcal A_{B'},\mathcal A_{Z'}$, for cut data $(A,B,Z)$ and $(A',B',Z')$. Then $F(\mathcal A_Y)\subset\mathcal A_{Y'}$, and $\partial_{A',B'}\circ\bar F_*=(F|_{\mathcal A_Y})_*\circ\partial_{A,B}$.

*Proof sketch.* [Support intersection](../supports/support-intersection.md) gives $F(\mathcal A_Y)\subset\mathcal A_{Y'}$. $F$ maps the ideal of $\mathcal A_Z$ into that of $\mathcal A_{Z'}$, so it induces $\bar F$ on the exterior quotients, which carries the cut square into the primed one. [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md) applies. Since $\bar F|_{\mathcal U_Y}\circ q=q'\circ F|_{\mathcal A_Y}$ strictly, $\bar F$ also commutes with the separated-support isomorphisms.

## Sources

- HS paper, Section 6

## Depends on

- [Cut boundary](cut-boundary.md)

## Proof depends on

- [Support intersection](../supports/support-intersection.md)
- [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
