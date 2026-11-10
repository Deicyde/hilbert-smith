---
article_id: af_c760165312de025f04962042
declaration: lemma
origin: bridged
---

# Naturality of the exterior quotient as a cut domain

Let $Z\subset X$ and $Z'\subset X'$ be closed and invariant, and let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor with $F(\mathcal A_Z)\subset\mathcal A_{Z'}$. Then
$$\bar F\circ j_Z=j_{Z'}\circ\bar F_{\mathcal B}:\mathcal B_{\mathbf G,Z}(X)\to\mathcal A_{X'}/\mathcal A_{Z'},$$
where $j_Z,j_{Z'}$ are the [exterior quotients as cut domains](exterior-cut-identification.md), $\bar F_{\mathcal B}:\mathcal B_{\mathbf G,Z}(X)\to\mathcal B_{\mathbf G',Z'}(X')$ is the [induced functor on exterior quotients](../supports/exterior-functor.md), and $\bar F:\mathcal A_X/\mathcal A_Z\to\mathcal A_{X'}/\mathcal A_{Z'}$ is the [induced functor on support quotients](cut-quotient-functor.md) for $S=X$, $S'=X'$.

*Proof sketch.*
1. The induced functor on support quotients applies with $S=X$ and $S'=X'$: every object of $\mathcal A_{\mathbf G'}(X')$ is $X'$-supported ([support subcategory of the whole space](../supports/support-whole.md)), so $F(\mathcal A_X)\subset\mathcal A_{X'}$.
2. On objects both composites send $M$ to $F(M)$.
3. On morphisms, every morphism of $\mathcal B_{\mathbf G,Z}(X)$ is a class $[u]$ of a morphism $u$ of $\mathcal A_{\mathbf G}(X)$ ([quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)). By induction on the quotient it suffices to compare the composites on $[u]$, and both give $[F(u)]$.

## Sources

- HS paper, Section 6
- New: split out of the identification of the exterior quotient with a cut domain, since the equation holds only after induction on the quotient.

## Depends on

- [The exterior quotient as a cut domain](exterior-cut-identification.md)
- [Induced functor on exterior quotients](../supports/exterior-functor.md)
- [Induced functor on support quotients](cut-quotient-functor.md)

## Proof depends on

- [Support subcategory](../supports/support-subcategory.md)
- [The support subcategory of the whole space](../supports/support-whole.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
