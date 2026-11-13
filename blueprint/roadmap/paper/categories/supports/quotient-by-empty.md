---
article_id: af_0f1c2108e45542fb5a287a8f
declaration: def
origin: bridged
statement: formalized
lean: HSP.quotientByEmptyIso
---

# Quotient by the empty support

Let $S\subset X$. Every $\varnothing$-supported object is eventually empty, hence a zero object, so the ideal of maps of $\mathcal A_S$ factoring through $\mathcal A_\varnothing$ is zero. The [quotient functor](../../l-theory/base/categories/filtration-quotient.md) $q:\mathcal A_S\to\mathcal A_S/\mathcal A_\varnothing$ by the subcategory $\mathcal A_\varnothing\subset\mathcal A_S$ of the [support filtration](support-filtration.md) is an isomorphism of duality categories: it is the identity on objects and bijective on morphisms, and its inverse $q^{-1}:\mathcal A_S/\mathcal A_\varnothing\to\mathcal A_S$, $M\mapsto M$, $[u]\mapsto u$, is a strict duality functor with $q^{-1}\circ q=\mathrm{id}$ and $q\circ q^{-1}=\mathrm{id}$.

*Proof sketch.*
1. Every object of $\mathcal A_\varnothing$ is a zero object. An object $W=(n_i,x_i)$ of the [support subcategory](support-subcategory.md) $\mathcal A_\varnothing$ has, for every $\varepsilon>0$, eventually all labels in the $\varepsilon$-thickening of $\varnothing$, which is empty; so $n_i=0$ for all large $i$. Then $1_W$ and $0$ are eventually equal matrices, so $1_W=0$ in the [asymptotic category](../asymptotic/asymptotic-category.md) by [equality of classes](../asymptotic/structure/class-eq.md).
2. Hence a morphism $u=ba$ factoring through $W\in\mathcal A_\varnothing$ is $b\,1_W\,a=0$. The ideal $I_{\mathcal A_\varnothing}$ is zero, so the quotient map on each hom-set is a bijection.
3. The inverse on hom-sets therefore defines $q^{-1}$. It preserves composition, identities, sums and transposes because $q$ does, and both composites are identity functors on objects and morphisms.

**Remark (not formalized).** The same argument, with $\mathcal A_{\mathbf G}(X)$ in place of $\mathcal A_S$, gives $\mathcal A_{\mathbf G}(X)\cong\mathcal A_{\mathbf G}(X)/\mathcal A_\varnothing$.

## Sources

- HS paper, Section 2
- New: a named step, used where a support quotient by $\mathcal A_\varnothing$ is undone.

## Depends on

- [Group sequence](../asymptotic/group-sequence.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [The support subcategory inside a support subcategory is additive](relative-support-additive.md)
- [Support subcategory](support-subcategory.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [The support subcategory is additive](support-dual-additive.md)
- [The quotient duality functor](../../l-theory/base/categories/quotient-duality-functor.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [Duality category of a dual-closed subcategory](../../l-theory/base/categories/dual-subcategory.md)
- [Strict duality functor](../../l-theory/base/categories/duality-functors/strict-duality-functor.md)

## Proof depends on

- [Free category of a finite group](../asymptotic/free-category.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
- [Equality of classes](../asymptotic/structure/class-eq.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [The quotient duality functor is strict](../../l-theory/base/categories/duality-functors/quotient-functor-strict.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
