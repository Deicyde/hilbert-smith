---
article_id: af_5b25da7a972fb98433e2e44d
declaration: def
origin: background
statement: formalized
lean: HSP.excisiveInterQuotIso
---

# Quotient of an excisive intersection

Let $S,A,B\subset X$ with $A$ compact, $B$ closed and $A\cap B=\varnothing$. Inside $\mathcal A_S$, let $\mathcal U_A$ and $\mathcal U_B$ be the [subcategories](../categories/supports/relative-support.md) of $A$- and $B$-supported objects, so that $\mathcal U_A\cap\mathcal U_B$ is a full additive subcategory of $\mathcal U_A$ closed under duality ([additive](../categories/supports/relative-intersection-additive.md)). The functor $\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)\to\mathcal A_A/\mathcal A_\varnothing$ between [quotients](../l-theory/base/categories/filtration-quotient.md), $M\mapsto M$, $[u]\mapsto[u]$, is a strict [duality functor](../l-theory/base/categories/duality-functor.md). Here $\mathcal A_\varnothing\subset\mathcal A_A$ is the [support subcategory](../categories/supports/relative-support.md) of $\varnothing$ inside $\mathcal A_A$.

*Proof sketch.*
1. An object $W$ of $\mathcal U_A\cap\mathcal U_B$ is $\varnothing$-supported. Choose $\delta>0$ with disjoint $\delta$-thickenings of $A$ and $B$, possible as $A$ is compact, $B$ is closed and $A\cap B=\varnothing$. Eventually every label of $W$ lies in both thickenings, so eventually $W$ has no basis elements, and its labels lie in every thickening of $\varnothing$.
2. Hence the functor is well defined: if $u$ factors through an object of $\mathcal U_A\cap\mathcal U_B$, it factors through an object of $\mathcal A_\varnothing$ by step 1.
3. It is the identity on objects and on representatives, so it is additive and $\mathbb Q$-linear and commutes with the transpose; so it is strict.

**Remark (not formalized).** If moreover $A\subset S$, the functor is an isomorphism of categories, with inverse $M\mapsto M$, $[u]\mapsto[u]$: a $\varnothing$-supported object is $B$-supported, and it is $A$-supported and lies in $\mathcal A_S$.

## Sources

- New: identifies the quotient realized by the [excision equivalence](../categories/supports/excision.md) with the quotient of a support subcategory.

## Depends on

- [Support subcategory inside a support subcategory](../categories/supports/relative-support.md)
- [Supported objects of a relative support subcategory are additive](../categories/supports/relative-intersection-additive.md)
- [Quotient by a filtration](../l-theory/base/categories/filtration-quotient.md)
- [Duality functor](../l-theory/base/categories/duality-functor.md)
