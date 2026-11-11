---
article_id: af_3c82264c2ae26e5d19c55827
declaration: instance
origin: background
statement: formalized
lean: HSP.instDualCatFullSubcategory
---

# Duality category of a dual-closed subcategory

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](dual-additive-subcategory.md) of a duality category $\mathcal A$. Then $\mathcal U$, with all morphisms of $\mathcal A$ between its objects, the sums and rational multiples of $\mathcal A$, and the duality $V\mapsto V^*$, $f\mapsto f^*$ of $\mathcal A$, is a [duality category](duality-category.md). The inclusion $\mathcal U\to\mathcal A$ is a strict [duality functor](duality-functor.md).

*Proof sketch.* (Proof obligations.) (1) $\mathcal U$ has finite biproducts: a zero object of $\mathcal A$ lying in $\mathcal U$ is a zero object of $\mathcal U$, and for $V,W\in\mathcal U$ a biproduct $P\in\mathcal U$ of $V$ and $W$ in $\mathcal A$ is one in $\mathcal U$, since its maps satisfy the biproduct equations, including $i_V\pi_V+i_W\pi_W=1_P$ for the inclusions $i_V,i_W$ and projections $\pi_V,\pi_W$, there too. (2) The duality restricts, since $\mathcal U^*\subset\mathcal U$, and its identities hold in $\mathcal U$ because they hold in $\mathcal A$. (3) The inclusion is $\mathbb Q$-linear and commutes with the duality on the nose.

## Sources

- Standard

## Depends on

- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](duality-category.md)
- [Duality functor](duality-functor.md)
