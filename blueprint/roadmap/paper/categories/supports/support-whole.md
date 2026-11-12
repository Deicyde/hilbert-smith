---
article_id: af_e865625882293d1a9cf50630
declaration: def
origin: bridged
statement: formalized
lean: HSP.supportWholeIso
---

# The support subcategory of the whole space

Every object of $\mathcal A_{\mathbf G}(X)$ lies in the [support subcategory](support-subcategory.md) $\mathcal A_X$, and the inclusion functor $\iota:\mathcal A_X\to\mathcal A_{\mathbf G}(X)$ is an isomorphism of duality categories. Its inverse $\iota^{-1}:\mathcal A_{\mathbf G}(X)\to\mathcal A_X$ is $M\mapsto M$, $u\mapsto u$; it is a strict duality functor, and $\iota^{-1}\circ\iota=\mathrm{id}$, $\iota\circ\iota^{-1}=\mathrm{id}$.

*Proof sketch.* All labels of an object lie in $X$, which is contained in each of its own $\varepsilon$-thickenings, so every object is $X$-supported. $\mathcal A_X$ is a full subcategory of the [asymptotic category](../asymptotic/asymptotic-category.md) closed under $M^*=M$, so $\iota$ is a strict duality functor, bijective on objects and the identity on morphisms. The inverse is the corestriction of the identity functor; it preserves composition, identities, sums and transposes, and both composites are identity functors.

**Remark (not formalized).** $\mathcal A_X$ and $\mathcal A_{\mathbf G}(X)$ are different categories with the same objects and maps; this article is the identification between them. On exterior quotients the same identification is the [exterior quotient as a cut domain](../cuts/exterior-cut-identification.md).

## Sources

- HS paper, Section 2
- New: a named identification of $\mathcal A_X$ with $\mathcal A_{\mathbf G}(X)$.

## Depends on

- [Support subcategory](support-subcategory.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Duality category of a dual-closed subcategory](../../l-theory/base/categories/dual-subcategory.md)
- [The support subcategory is additive](support-dual-additive.md)
- [Inclusion of a dual-closed subcategory](../../l-theory/base/categories/subcategory-inclusion.md)

## Proof depends on

- [The inclusion of a dual-closed subcategory is strict](../../l-theory/base/categories/duality-functors/inclusion-strict.md)
