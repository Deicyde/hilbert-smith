---
article_id: af_0f1c2108e45542fb5a287a8f
declaration: def
origin: bridged
---

# Quotient by the empty support

Let $S\subset X$ be closed and invariant. The [quotient functor](../../l-theory/base/categories/filtration-quotient.md) $q:\mathcal A_S\to\mathcal A_S/\mathcal A_\varnothing$ of the [support filtration](support-filtration.md) for $\varnothing\subset S$ is an isomorphism of duality categories: it is the identity on objects and bijective on morphisms, and its inverse $q^{-1}:\mathcal A_S/\mathcal A_\varnothing\to\mathcal A_S$, $M\mapsto M$, $[u]\mapsto u$, is a strict duality functor with $q^{-1}\circ q=\mathrm{id}$ and $q\circ q^{-1}=\mathrm{id}$. The case $S=X$ gives $\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G}(X)/\mathcal A_\varnothing$.

*Proof sketch.*
1. Every object of $\mathcal A_\varnothing$ is a zero object. An object $W=(n_i,x_i)$ of the [support subcategory](support-subcategory.md) $\mathcal A_\varnothing$ has, for every $\varepsilon>0$, eventually all labels in the $\varepsilon$-thickening of $\varnothing$, which is empty; so $n_i=0$ for all large $i$. Then $1_W$ and $0$ are eventually equal matrices, so $1_W=0$ in the [asymptotic category](../asymptotic/asymptotic-category.md).
2. Hence a morphism $u=ba$ factoring through $W\in\mathcal A_\varnothing$ is $b\,1_W\,a=0$. The ideal $I_{\mathcal A_\varnothing}$ is zero, so the quotient map on each hom-set is a bijection.
3. The inverse on hom-sets therefore defines $q^{-1}$. It preserves composition, identities, sums and transposes because $q$ does, and both composites are identity functors on objects and morphisms.

## Sources

- HS paper, Section 2
- New: a named step, used where a support quotient by $\mathcal A_\varnothing$ is undone.

## Depends on

- [Support subcategory](support-subcategory.md)
- [Support filtration](support-filtration.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

## Proof depends on

- [Asymptotic category](../asymptotic/asymptotic-category.md)
