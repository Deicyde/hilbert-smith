---
article_id: af_6a6fcd22c6b32eb9ee3179d3
declaration: def
origin: bridged
statement: formalized
lean: HSP.FiltQuot.liftDual
---

# Lift of a duality functor to a quotient

Let $\mathcal U\subset\mathcal A$ be a full additive subcategory closed under duality and $(F,\xi):\mathcal A\to\mathcal B$ a [duality functor](duality-functor.md) with $F(f_1)=F(f_2)$ whenever $f_1-f_2$ factors through an object of $\mathcal U$. Then $F$ induces a duality functor $\bar F:\mathcal A/\mathcal U\to\mathcal B$ on the [quotient](filtration-quotient.md), $\bar F(M)=F(M)$, $\bar F[f]=F(f)$, with the same duality isomorphisms $\xi_M$; and $\bar F\circ q=F$ for the quotient functor $q$.

*Proof sketch.* $\bar F$ is well defined on classes by hypothesis, and it is additive and $\mathbb Q$-linear because $F$ is and every map of $\mathcal A/\mathcal U$ is a class. Naturality of $\xi$ and $\xi^*=\xi$ are those of $F$, since $[f]^*=[f^*]$.

## Sources

- New: a named step, used for the identifications between quotients of support subcategories.

## Depends on

- [Quotient by a subcategory](filtration-quotient.md)
- [Duality functor](duality-functor.md)
- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](duality-category.md)
