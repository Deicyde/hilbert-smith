---
article_id: af_496e7bddd300ad9bc2861973
declaration: def
origin: bridged
statement: formalized
lean: HSP.cutSquare
---

# Cut square

Let $X$ be compact with an isometric $C_p$-action, let $A,B\subset X$ be closed and invariant, and let $Z\subset X$ be invariant. Put $S=A\cup B$, $Y=A\cap B$ and $\mathcal Q=\mathcal A_S/\mathcal A_Z$, the [quotient](../../l-theory/base/categories/filtration-quotient.md) of the [support subcategory](../supports/support-subcategory.md) $\mathcal A_S$ by its [subcategory](../supports/relative-support.md) $\mathcal A_Z\subset\mathcal A_S$. The cut square is an [excisive pair](../../l-theory/ultimate/boundary/excisive-pair.md) $(\mathcal U_A,\mathcal U_B)$ in $\mathcal Q$, where $\mathcal U_A$ and $\mathcal U_B$ are the predicates "$A$-supported" and "$B$-supported" ([supported objects of a support quotient](../supports/quotient-support.md)). Its [intersection](../../l-theory/ultimate/boundary/excisive-intersection.md) $\mathcal U_A\cap\mathcal U_B$ is the predicate "$Y$-supported". The cover $S$ need not be all of $X$, and $Z=\varnothing$ is allowed.

*Proof sketch.*
1. $\mathcal U_A$ and $\mathcal U_B$ are filtrations of $\mathcal Q$ by the [quotient support filtration](../supports/quotient-support-filtration.md) for $A$ and for $B$.
2. $\mathcal U_A\cap\mathcal U_B=\mathcal U_Y$ by [support intersection](../supports/support-intersection.md).
3. The functor $J:\mathcal A_A/\mathcal A_Z\to\mathcal U_A$ that is the identity on objects and on representatives is full, additive and strict, and every object of $\mathcal U_A$ is the image of an object. The $B$-supported objects of $\mathcal U_A$ form a filtration of $\mathcal U_A$: its chosen decompositions are the images under $J$ of those of the quotient support filtration of $\mathcal A_A/\mathcal A_Z$ by its $B$-supported objects, and each axiom transports along $J$.
4. Let $I:\mathcal Q/\mathcal U_B\to\mathcal A_S/\mathcal A_{B\cup Z}$ be the [iterated quotient](../supports/iterated-quotient.md), let $r_0$ be the inverse of the [excision equivalence](../supports/excision.md) $e_0$ for $A$ and $B\cup Z$, and let $K$ be the functor from the source of $e_0$ to $\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)$ that is the identity on objects and on representatives. $K$ is well defined: if a map $u$ between $A$-supported objects factors through a $(B\cup Z)$-supported object, then by the iterated quotient its class in $\mathcal Q$ factors through a $B$-supported object, so $u=v+w$ with $w$ factoring through $\mathcal A_Z$ and $v$ through a $B$-supported object; and $v$ factors through an $A$- and $B$-supported object, because the excision equivalence for $A$ and $B$ is faithful.
5. Put $r=K\circ r_0\circ I$. On representatives $I\circ e\circ K=e_0$ and $e\circ K=I^{-1}\circ e_0$. Hence the images of the unit and counit of $e_0$ under $K$ and under $I^{-1}$ are a unit $\mathrm{id}\cong r\circ e$ and a counit $e\circ r\cong\mathrm{id}$. They are unitary because $K$, $I$ and $I^{-1}$ are strict.

**Remark (not formalized).** In the uses $Z$ is also closed and $Z\subset A$, so that $\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)$ is identified with $\mathcal A_A/\mathcal A_{Y\cup Z}$. The construction uses neither.

## Sources

- HS paper, Section 6
- New: the exterior case reduced to ordinary excision for $A$ and $B\cup Z$, and the cover taken inside a closed invariant $S$ so that cuts can be iterated along a flag.

## Depends on

- [Support subcategory](../supports/support-subcategory.md)
- [Support subcategory inside a support subcategory](../supports/relative-support.md)
- [Supported objects of a support quotient](../supports/quotient-support.md)
- [Supported objects of a support quotient are additive](../supports/quotient-support-additive.md)
- [Support filtrations in a quotient](../supports/quotient-support-filtration.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Excisive pair of filtrations](../../l-theory/ultimate/boundary/excisive-pair.md)
- [Intersection of full subcategories](../../l-theory/ultimate/boundary/excisive-intersection.md)

## Proof depends on

- [Lift of a duality functor to a quotient](../../l-theory/base/categories/quotient-dual-lift.md)
- [Support intersection](../supports/support-intersection.md)
- [Iterated quotient](../supports/iterated-quotient.md)
- [Excision equivalence](../supports/excision.md)
- [Involution-invariant Karoubi filtration](../../l-theory/base/categories/karoubi-filtration.md)
- [Unitary natural isomorphism](../../l-theory/base/categories/unitary-isomorphism.md)
- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
- [The quotient duality functor](../../l-theory/base/categories/quotient-duality-functor.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
