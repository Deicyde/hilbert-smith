---
declaration: def
origin: bridged
---

# Cut square

Let $A,B,Z\subset X$ be closed and invariant with $A\cup B=X$ and $Z\subset A$. Put $Y=A\cap B$ and $\mathcal Q=\mathcal B_{\mathbf G,Z}(X)$. The cut square is the [excisive pair](../l-theory/ultimate/excisive-pair.md) $(\mathcal U_A,\mathcal U_B)$ in $\mathcal Q$, where $\mathcal U_A$ and $\mathcal U_B$ are the predicates "$A$-supported" and "$B$-supported". Its intersection $\mathcal U_A\cap\mathcal U_B$ is the predicate "$Y$-supported".

*Proof sketch.*
1. $\mathcal U_A$ and $\mathcal U_B$ are filtrations of $\mathcal Q$ by the [quotient support filtration](quotient-support-filtration.md) with $S=X$.
2. $\mathcal U_A\cap\mathcal U_B=\mathcal U_Y$ by [support intersection](support-intersection.md).
3. The full subcategory $\mathcal U_A$ equals $\mathcal A_A/\mathcal A_Z$ on the nose, because $\mathcal A_Z\subset\mathcal A_A$ is full and $Z\subset A$. So $\mathcal U_Y\subset\mathcal U_A$ is the quotient support filtration for $Y,Z\subset A$.
4. The [iterated quotient](iterated-quotient.md) for $(A;Y,Z)$ and for $(X;B,Z)$ identifies $e:\mathcal U_A/\mathcal U_Y\to\mathcal Q/\mathcal U_B$ with the [excision equivalence](excision.md) for $A$ and $B\cup Z$. Their intersection is $Y\cup Z$ (as $Z\subset A$) and their union is $X$. The inverse, unit and counit transport along these identity-on-objects isomorphisms.

## Sources

- HS paper, Section 6
- New: the exterior case reduced to ordinary excision for $A$ and $B\cup Z$.

## Depends on

- [Exterior quotient](exterior-quotient.md)
- [Excisive pair of filtrations](../l-theory/ultimate/excisive-pair.md)

## Proof depends on

- [Quotient support filtration](quotient-support-filtration.md)
- [Support intersection](support-intersection.md)
- [Iterated quotient](iterated-quotient.md)
- [Excision equivalence](excision.md)
