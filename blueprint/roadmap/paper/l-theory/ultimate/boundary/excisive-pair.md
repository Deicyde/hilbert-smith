---
article_id: af_5897f0e625584e0e0b88c232
declaration: structure
origin: bridged
statement: formalized
lean: HSP.ExcisivePair
---

# Excisive pair of filtrations

An *excisive pair* in $\mathcal A$ consists of
- involution-invariant Karoubi filtrations $\mathcal U_A,\mathcal U_B\subset\mathcal A$ such that $\mathcal U_Y:=\mathcal U_A\cap\mathcal U_B$ (the full subcategory of objects lying in both) is an involution-invariant Karoubi filtration of $\mathcal U_A$;
- a duality functor $r:\mathcal A/\mathcal U_B\to\mathcal U_A/\mathcal U_Y$;
- unitary natural isomorphisms $\mathrm{id}\cong r\circ e$ and $e\circ r\cong\mathrm{id}$,

where $e:\mathcal U_A/\mathcal U_Y\to\mathcal A/\mathcal U_B$ is the strict duality functor that is the identity on objects and sends the class of a morphism modulo $\mathcal U_Y$ to its class modulo $\mathcal U_B$. It is well defined because a morphism that factors through an object of $\mathcal U_Y$ factors through an object of $\mathcal U_B$. By construction $e\circ q_Y=q_B\circ i_A$, where $i_A:\mathcal U_A\to\mathcal A$ is the inclusion and $q_Y,q_B$ are the quotient functors.

## Sources

- HS paper, Section 2 and Section 6 (excision for support filtrations, ordinary and exterior)

## Depends on

- [Intersection of full subcategories](excisive-intersection.md)
- [Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Full subcategory closed under duality](../../base/categories/dual-subcategory.md)
