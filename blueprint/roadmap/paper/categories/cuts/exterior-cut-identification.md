---
article_id: af_ef3cf69659baf1ff67e3b9b6
declaration: def
origin: bridged
statement: formalized
lean: HSP.exteriorCutIdent
---

# The exterior quotient as a cut domain

Let $Z\subset X$. The functor $j_Z:\mathcal B_{\mathbf G,Z}(X)\to\mathcal A_X/\mathcal A_Z$ from the [exterior quotient](../supports/exterior-quotient.md) to the quotient of the [support subcategory](../supports/support-subcategory.md) $\mathcal A_X$ by its subcategory $\mathcal A_Z\subset\mathcal A_X$ of the [support filtration](../supports/support-filtration.md) is $M\mapsto M$, $[u]\mapsto[u]$; that is, $j_Z\circ q=q'\circ\iota^{-1}$ for the quotient functors $q,q'$ and the corestriction $\iota^{-1}:\mathcal A_{\mathbf G}(X)\to\mathcal A_X$ of the identity. It is a strict duality functor.

*Proof sketch.* Every object of $\mathcal A_{\mathbf G}(X)$ is $X$-supported ([support subcategory of the whole space](../supports/support-whole.md)), and $\mathcal A_X\subset\mathcal A_{\mathbf G}(X)$ is full, so the two quotients have the same objects, the same hom-sets and the same ideal of maps factoring through $\mathcal A_Z$. Hence $j_Z$ is well defined and preserves composition, identities and transposes.

**Remark (not formalized).** The functor back, also the identity on objects and representatives, is inverse to $j_Z$. The iterated cut uses only $j_Z$. Its commutation with induced functors is the [naturality of the exterior quotient as a cut domain](exterior-cut-naturality.md).

## Sources

- HS paper, Section 6
- New: a named identification, because the support subcategory $\mathcal A_X$ and $\mathcal A_{\mathbf G}(X)$ are different categories with the same objects and maps.

## Depends on

- [Support subcategory inside a support subcategory](../supports/relative-support.md)
- [The support subcategory inside a support subcategory is additive](../supports/relative-support-additive.md)
- [Exterior quotient](../supports/exterior-quotient.md)
- [Support subcategory](../supports/support-subcategory.md)
- [The support subcategory of the whole space](../supports/support-whole.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [Group sequence](../asymptotic/group-sequence.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [The support subcategory is additive](../supports/support-dual-additive.md)
- [Duality category of a dual-closed subcategory](../../l-theory/base/categories/dual-subcategory.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Strict duality functor](../../l-theory/base/categories/duality-functors/strict-duality-functor.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Inclusion of a dual-closed subcategory](../../l-theory/base/categories/subcategory-inclusion.md)

## Proof depends on

- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
