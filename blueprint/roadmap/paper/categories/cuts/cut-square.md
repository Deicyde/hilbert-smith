---
article_id: af_496e7bddd300ad9bc2861973
declaration: def
origin: bridged
---

# Cut square

Let $A,B,Z\subset X$ be closed and invariant with $Z\subset A$. Put $S=A\cup B$, $Y=A\cap B$ and $\mathcal Q=\mathcal A_S/\mathcal A_Z$, the quotient of the [support subcategory](../supports/support-subcategory.md) $\mathcal A_S$ by the [support filtration](../supports/support-filtration.md) for $Z\subset S$. The cut square is the [excisive pair](../../l-theory/ultimate/boundary/excisive-pair.md) $(\mathcal U_A,\mathcal U_B)$ in $\mathcal Q$, where $\mathcal U_A$ and $\mathcal U_B$ are the predicates "$A$-supported" and "$B$-supported". Its intersection $\mathcal U_A\cap\mathcal U_B$ is the predicate "$Y$-supported". The cover $S$ need not be all of $X$, and $Z=\varnothing$ is allowed.

*Proof sketch.*
1. $\mathcal U_A$ and $\mathcal U_B$ are filtrations of $\mathcal Q$ by the [quotient support filtration](../supports/quotient-support-filtration.md) for $A,Z\subset S$ and for $B,Z\subset S$.
2. $\mathcal U_A\cap\mathcal U_B=\mathcal U_Y$ by [support intersection](../supports/support-intersection.md).
3. The full subcategory $\mathcal U_A$ of $\mathcal Q$ and $\mathcal A_A/\mathcal A_Z$ are isomorphic by strict duality functors that are the identity on objects and on representatives: the hom-sets agree because $\mathcal A_A\subset\mathcal A_S$ is full and $Z\subset A$, so a map between $A$-supported objects factors through a $Z$-supported object in $\mathcal A_S$ exactly when it does in $\mathcal A_A$. Transporting the quotient support filtration for $Y,Z\subset A$ along this isomorphism makes $\mathcal U_Y\subset\mathcal U_A$ a filtration; the chosen decompositions are the same idempotents, so each axiom transports verbatim.
4. The [iterated quotient](../supports/iterated-quotient.md) for $(A;Y,Z)$ and for $(S;B,Z)$, composed with step 3, identifies $e:\mathcal U_A/\mathcal U_Y\to\mathcal Q/\mathcal U_B$ with the [excision equivalence](../supports/excision.md) for $A$ and $B\cup Z$, whose intersection is $Y\cup Z$ (as $Z\subset A$) and whose union is $S$. All these identifications are the identity on objects and on representatives, so the excision equivalence's inverse $r$ and its unitary unit and counit transport to the cut square unchanged.

## Sources

- HS paper, Section 6
- New: the exterior case reduced to ordinary excision for $A$ and $B\cup Z$, and the cover taken inside a closed invariant $S$ so that cuts can be iterated along a flag.

## Depends on

- [Support subcategory](../supports/support-subcategory.md)
- [Support filtration](../supports/support-filtration.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)
- [Excisive pair of filtrations](../../l-theory/ultimate/boundary/excisive-pair.md)

## Proof depends on

- [Quotient support filtration](../supports/quotient-support-filtration.md)
- [Support intersection](../supports/support-intersection.md)
- [Iterated quotient](../supports/iterated-quotient.md)
- [Excision equivalence](../supports/excision.md)
