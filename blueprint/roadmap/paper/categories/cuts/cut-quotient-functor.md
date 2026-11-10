---
article_id: af_77738c3a3ed7967b1adfb8cc
declaration: def
origin: bridged
---

# Induced functor on support quotients

Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor, and let $Z\subset S\subset X$ and $Z'\subset S'\subset X'$ be closed and invariant with $F(\mathcal A_S)\subset\mathcal A_{S'}$ and $F(\mathcal A_Z)\subset\mathcal A_{Z'}$. The induced functor $\bar F:\mathcal A_S/\mathcal A_Z\to\mathcal A_{S'}/\mathcal A_{Z'}$ on the [quotients](../../l-theory/base/categories/filtration-quotient.md) by the [support filtrations](../supports/support-filtration.md) is $M\mapsto F(M)$, $[u]\mapsto[F(u)]$. It is a strict duality functor, and $\bar F\circ q=q'\circ F|_{\mathcal A_S}$ for the quotient functors $q:\mathcal A_S\to\mathcal A_S/\mathcal A_Z$ and $q':\mathcal A_{S'}\to\mathcal A_{S'}/\mathcal A_{Z'}$.

*Proof sketch.* If $u=ba$ through $W\in\mathcal A_Z$, then $F(u)=F(b)F(a)$ through $F(W)\in\mathcal A_{Z'}$, so $\bar F$ is well defined. It is $\mathbb Q$-linear and commutes with composition, identities and transposes because $F$ does. Both sides of $\bar F\circ q=q'\circ F|_{\mathcal A_S}$ send $M$ to $F(M)$ and $u$ to $[F(u)]$.

**Remark (not formalized).** For $S=X$ this is the [induced functor on exterior quotients](../supports/exterior-functor.md) read through the [exterior quotient as a cut domain](exterior-cut-identification.md): $\bar F\circ j_Z=j_{Z'}\circ\bar F_{\mathcal B}$ is the [naturality of the exterior quotient as a cut domain](exterior-cut-naturality.md). With $Z=Z'=\varnothing$ it is the functor that the iteration of cuts along a flag composes with the quotient functors $\mathcal A_{Y_m}\to\mathcal A_{Y_m}/\mathcal A_\varnothing$.

## Sources

- HS paper, Section 6

## Depends on

- [Support subcategory](../supports/support-subcategory.md)
- [Support filtration](../supports/support-filtration.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
