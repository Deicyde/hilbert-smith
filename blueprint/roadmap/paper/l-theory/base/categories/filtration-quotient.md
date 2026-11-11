---
article_id: af_83605d31b138e8b58dbb6c6e
declaration: abbrev
origin: background
statement: formalized
lean: HSP.FiltQuot
---

# Quotient by a subcategory

Let $\mathcal U\subset\mathcal A$ be a [full additive subcategory with $\mathcal U^*\subset\mathcal U$](dual-additive-subcategory.md). Let $I_{\mathcal U}(M,N)$ be the set of maps $M\to N$ that factor through an object of $\mathcal U$. Then $I_{\mathcal U}$ is a $\mathbb Q$-linear ideal closed under $*$: if $f$ factors through $V$ and $g$ through $W$, then $f+g$ factors through a sum of $V$ and $W$ in $\mathcal U$, and $f=ba$ gives $f^*=a^*b^*$ through $V^*$. So $\mathcal A/\mathcal U$, with the objects of $\mathcal A$ and $\mathrm{Hom}(M,N)/I_{\mathcal U}(M,N)$, is a duality category: its sums are the images of those of $\mathcal A$, and its duality is $M^*$ on objects and $[f]^*=[f^*]$ on morphisms. The quotient functor $q:\mathcal A\to\mathcal A/\mathcal U$, $M\mapsto M$, $f\mapsto[f]$, is a strict duality functor.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- HS paper, Section 2

## Depends on

- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](duality-category.md)
- [Duality functor](duality-functor.md)
