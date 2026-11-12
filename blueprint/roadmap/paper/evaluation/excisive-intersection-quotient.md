---
article_id: af_5b25da7a972fb98433e2e44d
declaration: def
origin: background
statement: formalized
lean: HSP.excisiveInterQuotIso
---

# Quotient of an excisive intersection

Let $S,A,B,C\subset X$ with $A$ compact, $B$ closed, $A\subset S$ and $A\cap B=C$ (for instance $A$ and $B$ closed in a compact $X$, as in the standing assumptions; $C=\varnothing$ when $A$ and $B$ are disjoint). Inside $\mathcal A_S$, let $\mathcal U_A$ and $\mathcal U_B$ be the [subcategories](../categories/supports/relative-support.md) of $A$- and $B$-supported objects, so that $\mathcal U_A\cap\mathcal U_B$ is a full additive subcategory of $\mathcal U_A$ closed under duality ([additive](../categories/supports/relative-intersection-additive.md)), and let $\mathcal A_C\subset\mathcal A_A$ be the [support subcategory](../categories/supports/relative-support.md) of $C$ inside $\mathcal A_A$. Then the [quotients](../l-theory/base/categories/filtration-quotient.md) $\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)$ and $\mathcal A_A/\mathcal A_C$ are isomorphic duality categories, by the identity on objects and on representatives. Precisely, there is a pair $(e,e')$ of [duality functors](../l-theory/base/categories/duality-functor.md)
$$e:\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)\to\mathcal A_A/\mathcal A_C,\qquad e':\mathcal A_A/\mathcal A_C\to\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)$$
such that:
1. $e$ is $M\mapsto M$, $[u]\mapsto[u]$: composed with the quotient functor of $\mathcal U_A$ it equals the inclusion $\mathcal U_A\to\mathcal A_A$ followed by the quotient functor of $\mathcal A_A$;
2. $e'$ is $M\mapsto M$, $[u]\mapsto[u]$: composed with the quotient functor of $\mathcal A_A$ it equals the inclusion $\mathcal A_A\to\mathcal U_A$ (an object of $\mathcal A_A$ is $S$-supported, as $A\subset S$) followed by the quotient functor of $\mathcal U_A$;
3. $e$ and $e'$ are strict;
4. $e'\circ e$ and $e\circ e'$ are the identity functors.

*Proof sketch.*
1. For every $\varepsilon>0$ there is $\delta>0$ with $N_\delta(A)\cap N_\delta(B)\subset N_\varepsilon(A\cap B)$, where $N_r$ is the open $r$-thickening. The set $K=A\setminus N_{\varepsilon/2}(A\cap B)$ is compact and disjoint from the closed set $B$, so some $\delta\le\varepsilon/2$ gives disjoint $\delta$-thickenings of $K$ and $B$. If $x\in N_\delta(A)\cap N_\delta(B)$, pick $a\in A$ with $d(x,a)<\delta$; then $a\notin K$, so $a$ is within $\varepsilon/2$ of $A\cap B$ and $x$ within $\varepsilon$. (If $A$ or $B$ is empty, so is $N_\delta(A)\cap N_\delta(B)$.)
2. Hence an object $W$ of $\mathcal U_A\cap\mathcal U_B$ is $C$-supported: given $\varepsilon$, eventually every label of $W$ lies in $N_\delta(A)\cap N_\delta(B)\subset N_\varepsilon(C)$. So $e$ is well defined: if $u$ factors through an object of $\mathcal U_A\cap\mathcal U_B$, it factors through an object of $\mathcal A_C$.
3. Conversely $e'$ is well defined: if $u$ factors through an object of $\mathcal A_C$, that object is $B$-supported because $C\subset B$, and it lies in $\mathcal U_A$; so $u$ factors through an object of $\mathcal U_A\cap\mathcal U_B$.
4. The inclusions $\mathcal U_A\to\mathcal A_A$ and $\mathcal A_A\to\mathcal U_A$ are the identity on objects and maps, so they are additive and commute with the transpose: they are mutually inverse strict duality functors. Composed with the [quotient duality functors](../l-theory/base/categories/quotient-duality-functor.md), they induce $e$ and $e'$ by steps 2 and 3 ([lift to a quotient](../l-theory/base/categories/quotient-dual-lift.md)), which are strict and satisfy items 1 and 2. By these characterizations both composites agree with the identity after the quotient functor, hence are the identity functors.

## Sources

- New: identifies the source of the [excision equivalence](../categories/supports/excision.md) for compact $A\subset S$ and closed $B$ with the quotient $\mathcal A_A/\mathcal A_{A\cap B}$ of a support subcategory.

## Depends on

- [Support subcategory inside a support subcategory](../categories/supports/relative-support.md)
- [Supported objects of a relative support subcategory are additive](../categories/supports/relative-intersection-additive.md)
- [Intersection of full subcategories](../l-theory/ultimate/boundary/excisive-intersection.md)
- [Quotient by a filtration](../l-theory/base/categories/filtration-quotient.md)
- [Duality functor](../l-theory/base/categories/duality-functor.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Group sequence](../categories/asymptotic/group-sequence.md)

## Proof depends on

- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Small Q-linear category with strict duality](../l-theory/base/categories/duality-category.md)
- [Additive subcategory closed under duality](../l-theory/base/categories/dual-additive-subcategory.md)
- [Maps factoring through a subcategory](../l-theory/base/categories/filtration-ideal.md)
- [Duality category of a dual-closed subcategory](../l-theory/base/categories/dual-subcategory.md)
- [The quotient duality functor](../l-theory/base/categories/quotient-duality-functor.md)
- [Lift of a duality functor to a quotient](../l-theory/base/categories/quotient-dual-lift.md)
