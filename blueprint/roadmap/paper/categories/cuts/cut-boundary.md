---
article_id: af_e3984ce72babfe6a50343183
declaration: def
origin: bridged
---

# Cut boundary

Let $A,B,Z\subset X$ be closed and invariant with $Z\subset A$ and $Z\cap B=\varnothing$. Put $S=A\cup B$ and $Y=A\cap B$, so that $Y\cap Z=\varnothing$. The cut boundary
$$\partial_{A,B}:\mathbb L_k(\mathcal A_S/\mathcal A_Z)\to\mathbb L_{k-1}(\mathcal A_Y)$$
is the [excision boundary](../../l-theory/ultimate/boundary/excision-boundary.md) of the [cut square](cut-square.md), $\mathbb L_k(\mathcal A_S/\mathcal A_Z)\to\mathbb L_{k-1}(\mathcal U_Y)$, followed by the map induced by $\sigma:\mathcal U_Y\to\mathcal A_Y$, the inverse in [separated support](../supports/quotient-separation-iso.md) for $Y,Z\subset S$.

**Remark (not formalized).** Two special cases feed the iteration along a flag. For $S=X$, the domain receives $\mathbb L_k(\mathcal B_{\mathbf G,Z}(X))$ by the map induced by $j_Z$, the [exterior quotient as a cut domain](exterior-cut-identification.md). For $Z=\varnothing$, it receives $\mathbb L_k(\mathcal A_S)$ by the map induced by the [quotient functor](../../l-theory/base/categories/filtration-quotient.md) $q:\mathcal A_S\to\mathcal A_S/\mathcal A_\varnothing$. Both connecting functors commute strictly with the functors induced by support-preserving strict duality functors ([induced functor on support quotients](cut-quotient-functor.md)). Since the target $\mathcal A_Y$ is again a support subcategory of $\mathcal A_{\mathbf G}(X)$, the next cut, inside $Y$, applies directly.

## Sources

- HS paper, Section 6

## Depends on

- [Cut square](cut-square.md)
- [Separated support in a quotient](../supports/quotient-separation-iso.md)
- [Excision boundary](../../l-theory/ultimate/boundary/excision-boundary.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
