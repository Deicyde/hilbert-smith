---
article_id: af_97523a9f8f15ccaf560a9f32
declaration: def
origin: bridged
---

# Excision equivalence

Let $A,B\subset X$ be closed and invariant. They need not cover $X$. The excision equivalence is the duality equivalence $e:\mathcal A_A/\mathcal A_{A\cap B}\to\mathcal A_{A\cup B}/\mathcal A_B$ induced by inclusion. Both quotients are taken by [support filtrations](support-filtration.md). Its inverse is $R(M)=M_A$, $R[u]=[\pi u\iota]$, and its unit and counit are unitary. Here, for $M\in\mathcal A_{A\cup B}$ with a chosen null $a$ such that eventually all $x_i(k)\in\overline N_{a_i}(A\cup B)$, $M_A$ keeps the $k$ with $x_i(k)\in\overline N_{a_i}(A)$, and $\iota,\pi$ are its coordinate inclusion and projection.

*Proof sketch.*
1. The complement $M_{\rm far}$ of $M_A$ has its labels in $\overline N_{a_i}(B)$, so it is $B$-supported. Hence $[\iota]:M_A\to M$ is an isomorphism in $\mathcal A_{A\cup B}/\mathcal A_B$ with inverse $[\iota]^{T}=[\pi]$, because $\pi\iota=1$ and $1-\iota\pi$ factors through $M_{\rm far}$. This is the counit.
2. For $M\in\mathcal A_A$, the summand $M_{\rm far}$ is $A$- and $B$-supported, so by [support intersection](support-intersection.md) it lies in $\mathcal A_{A\cap B}$. Hence $[\pi]:M\to M_A$ is an isomorphism there with inverse $[\pi]^{T}=[\iota]$. This is the unit.
3. $R$ is well defined: if $u$ factors through $\mathcal A_B$ then $\pi u\iota$ does too, and the rows of the middle object hit by $\pi u\iota$ are near $A$ and near $B$. So $\pi u\iota$ factors through $\mathcal A_{A\cap B}$, by the [support ideal](support-ideal.md) and support intersection. $R$ is strict because $(\pi u\iota)^T=\pi u^T\iota$.
4. $R$ is a functor, and the unit and counit are natural. The composition defect $R(vu)-R(v)R(u)=\pi v(1-\iota\pi)u\iota$ factors through a far summand, which is $B$-supported, and its source and target are $A$-supported; by step 3's argument it factors through $\mathcal A_{A\cap B}$. The counit's naturality defect $(1-\iota\pi)u\iota$ factors through a far summand, so it lies in the ideal of $\mathcal A_B$. The unit is handled in the same way as the composition defect.
5. The unit and counit are unitary natural isomorphisms, since each component's inverse is its transpose and $e$, $R$ are strict. The triangle identities hold on representatives, because every component is a coordinate matrix.

## Sources

- HS paper, Section 2

## Depends on

- [Support filtration](support-filtration.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Unitary isomorphism](../../l-theory/base/categories/unitary-isomorphism.md)

## Proof depends on

- [Support ideal](support-ideal.md)
- [Support intersection](support-intersection.md)
