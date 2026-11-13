---
article_id: af_83605d31b138e8b58dbb6c6e
declaration: abbrev
origin: background
statement: formalized
lean: HSP.FiltQuot
---

# Quotient by a subcategory

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](dual-additive-subcategory.md). The [maps factoring through an object of $\mathcal U$](filtration-ideal.md) form a $\mathbb Q$-linear ideal $I_{\mathcal U}$ closed under $*$ ([Maps factoring through a dual-closed subcategory form an ideal](filtration-ideal-closure.md)). So $\mathcal A/\mathcal U$, with the objects of $\mathcal A$ and $\mathrm{Hom}(M,N)/I_{\mathcal U}(M,N)$, is a duality category: its sums are the images of those of $\mathcal A$, and its duality is $M^*$ on objects and $[f]^*=[f^*]$ on morphisms. The quotient functor $\mathcal A\to\mathcal A/\mathcal U$ is $M\mapsto M$, $f\mapsto[f]$; two maps have the same class if and only if their difference lies in $I_{\mathcal U}$.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 2

## Depends on

## Proof depends on

- [Maps factoring through a subcategory](filtration-ideal.md)
- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](duality-category.md)
- [Maps factoring through a dual-closed subcategory form an ideal](filtration-ideal-closure.md)
