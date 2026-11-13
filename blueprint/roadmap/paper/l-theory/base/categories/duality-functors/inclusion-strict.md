---
article_id: af_70a68b820a90438fb0bdcb4b
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualSubcategory.incl_isStrict
proof: formalized
---

# The inclusion of a dual-closed subcategory is strict

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](../dual-additive-subcategory.md). The [inclusion](../subcategory-inclusion.md) $i:\mathcal U\to\mathcal A$ is a [strict](strict-duality-functor.md) duality functor.

*Proof sketch.* The duality of $\mathcal U$ is that of $\mathcal A$, so $i(V^*)=i(V)^*$; the duality isomorphism of $i$ is the identity by definition.

## Sources

- Standard

## Depends on

- [Inclusion of a dual-closed subcategory](../subcategory-inclusion.md)
- [Strict duality functor](strict-duality-functor.md)
- [Additive subcategory closed under duality](../dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../duality-category.md)
- [Duality category of a dual-closed subcategory](../dual-subcategory.md)

## Proof depends on

- [Duality functor](../duality-functor.md)
