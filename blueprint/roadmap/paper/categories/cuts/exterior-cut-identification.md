---
article_id: af_ef3cf69659baf1ff67e3b9b6
declaration: def
origin: bridged
---

# The exterior quotient as a cut domain

Let $Z\subset X$ be closed and invariant. The functor $j_Z:\mathcal B_{\mathbf G,Z}(X)\to\mathcal A_X/\mathcal A_Z$ from the [exterior quotient](../supports/exterior-quotient.md) to the quotient of the [support subcategory](../supports/support-subcategory.md) $\mathcal A_X$ by the [support filtration](../supports/support-filtration.md) for $Z\subset X$ is $M\mapsto M$, $[u]\mapsto[u]$. It is a strict duality functor. If $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ is a strict duality functor with $F(\mathcal A_Z)\subset\mathcal A_{Z'}$, then
$$\bar F\circ j_Z=j_{Z'}\circ\bar F_{\mathcal B},$$
where $\bar F_{\mathcal B}:\mathcal B_{\mathbf G,Z}(X)\to\mathcal B_{\mathbf G',Z'}(X')$ is the [induced functor on exterior quotients](../supports/exterior-functor.md) and $\bar F:\mathcal A_X/\mathcal A_Z\to\mathcal A_{X'}/\mathcal A_{Z'}$ the [induced functor on support quotients](cut-quotient-functor.md).

*Proof sketch.* Every object of $\mathcal A_{\mathbf G}(X)$ is $X$-supported, and $\mathcal A_X\subset\mathcal A_{\mathbf G}(X)$ is full, so the two quotients have the same objects, the same hom-sets and the same ideal of maps factoring through $\mathcal A_Z$. Hence $j_Z$ is well defined and preserves composition, identities and transposes. Both sides of the displayed equation send $M$ to $F(M)$ and $[u]$ to $[F(u)]$; $F(\mathcal A_X)\subset\mathcal A_{X'}$ holds because every object of $\mathcal A_{\mathbf G'}(X')$ is $X'$-supported.

**Remark (not formalized).** The functor back, also the identity on objects and representatives, is inverse to $j_Z$. The iterated cut uses only $j_Z$.

## Sources

- HS paper, Section 6
- New: a named identification, because the support subcategory $\mathcal A_X$ and $\mathcal A_{\mathbf G}(X)$ are different categories with the same objects and maps.

## Depends on

- [Exterior quotient](../supports/exterior-quotient.md)
- [Support subcategory](../supports/support-subcategory.md)
- [Support filtration](../supports/support-filtration.md)
- [Induced functor on exterior quotients](../supports/exterior-functor.md)
- [Induced functor on support quotients](cut-quotient-functor.md)
