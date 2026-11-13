---
article_id: af_fca3d9de050b034694f99f64
declaration: lemma
origin: background
statement: formalized
lean: HSP.FiltQuot.q_isStrict
proof: formalized
---

# The quotient duality functor is strict

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](../dual-additive-subcategory.md). The [quotient duality functor](../quotient-duality-functor.md) $q:\mathcal A\to\mathcal A/\mathcal U$ is [strict](strict-duality-functor.md).

*Proof sketch.* $q$ is the identity on objects and the duality of $\mathcal A/\mathcal U$ is that of $\mathcal A$ on objects, so $q(M^*)=q(M)^*$; the duality isomorphism of $q$ is the identity by definition.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [The quotient duality functor](../quotient-duality-functor.md)
- [Strict duality functor](strict-duality-functor.md)
- [Additive subcategory closed under duality](../dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../duality-category.md)
- [Quotient by a subcategory](../filtration-quotient.md)

## Proof depends on

- [Duality functor](../duality-functor.md)
