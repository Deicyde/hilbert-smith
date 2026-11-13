---
article_id: af_97523a9f8f15ccaf560a9f32
declaration: def
origin: bridged
statement: formalized
lean: HSP.excision
---

# Excision equivalence

Let the action be isometric, let $A,B\subset X$ with $B$ invariant, and let $S\subset X$ with $S\subset A\cup B$ (for example $S=A\cup B$; the sets need not cover $X$). Inside $\mathcal A_S$, let $\mathcal U_A$ and $\mathcal U_B$ be the [subcategories](relative-support.md) of $A$- and $B$-supported objects, and let $\mathcal U_A\cap\mathcal U_B$ be the [intersection](../../l-theory/ultimate/boundary/excisive-intersection.md), the $B$-supported objects of $\mathcal U_A$ ([additive](relative-intersection-additive.md)). The excision equivalence is the duality equivalence $e:\mathcal U_A/(\mathcal U_A\cap\mathcal U_B)\to\mathcal A_S/\mathcal A_B$ induced by inclusion (the strict duality functor of an [excisive pair](../../l-theory/ultimate/boundary/excisive-pair.md)). Its target is the quotient by a subcategory of a [support filtration](support-filtration.md). The inverse of $e$ is the duality functor $R(M)=M_A$, $R[u]=[\pi u\iota]$, with a unitary unit $\mathrm{id}\cong R\circ e$ (components $[\pi]$) and a unitary counit $e\circ R\cong\mathrm{id}$ (components $[\iota]$). Here, for $M\in\mathcal A_S$ with a chosen null $a$ such that eventually all $x_i(k)\in\overline N_{a_i}(S)$, $M_A$ keeps the $k$ with $x_i(k)\in\overline N_{a_i}(A)$, and $\iota,\pi$ are its coordinate inclusion and projection. The source of $e$ is a quotient of $\mathcal U_A$, not in general of a support subcategory of $A$; when $A$ is compact, $B$ is closed and $A\subset S$, it is identified with $\mathcal A_A/\mathcal A_{A\cap B}$ by the [quotient of an excisive intersection](../../evaluation/excisive-intersection-quotient.md).

*Proof sketch.*
1. The complement $M_{\rm far}$ of $M_A$ eventually has its labels in $\overline N_{a_i}(B)$, since $\overline N_{a_i}(S)\subset\overline N_{a_i}(A)\cup\overline N_{a_i}(B)$, so it is $B$-supported. Hence $[\iota]:M_A\to M$ is an isomorphism in $\mathcal A_S/\mathcal A_B$ with inverse $[\iota]^{T}=[\pi]$, because $\pi\iota=1$ and $1-\iota\pi$ factors through $M_{\rm far}$. This is the counit.
2. For $M\in\mathcal U_A$, the summand $M_{\rm far}$ is $A$- and $B$-supported, so it lies in $\mathcal U_A\cap\mathcal U_B$. Hence $[\pi]:M\to M_A$ is an isomorphism there with inverse $[\pi]^{T}=[\iota]$. This is the unit.
3. $R$ is well defined: if $u$ factors through $\mathcal A_B$ then $\pi u\iota$ does too, and the rows of the middle object hit by $\pi u\iota$ are near $A$ and near $B$. So $\pi u\iota$ factors through an object of $\mathcal U_A\cap\mathcal U_B$, by the [support ideal](support-ideal.md): restrict its source to its nonzero columns. $R$ is strict because $(\pi u\iota)^T=\pi u^T\iota$.
4. $R$ is a functor, and the unit and counit are natural. The composition defect $R(vu)-R(v)R(u)=\pi v(1-\iota\pi)u\iota$ factors through a far summand, which is $B$-supported, and its source and target are $A$-supported; by step 3's argument it factors through $\mathcal U_A\cap\mathcal U_B$. The counit's naturality defect $(1-\iota\pi)u\iota$ factors through a far summand, so it lies in the ideal of $\mathcal A_B$. The unit is handled in the same way as the composition defect.
5. The unit and counit are unitary natural isomorphisms, since each component's inverse is its transpose and $e$, $R$ are strict.

## Sources

- HS paper, Section 2

## Depends on

- [Intersection of full subcategories](../../l-theory/ultimate/boundary/excisive-intersection.md)
- [Support subcategory inside a support subcategory](relative-support.md)
- [The support subcategory inside a support subcategory is additive](relative-support-additive.md)
- [Supported objects of a relative support subcategory are additive](relative-intersection-additive.md)
- [Excisive pair of filtrations](../../l-theory/ultimate/boundary/excisive-pair.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Unitary isomorphism](../../l-theory/base/categories/unitary-isomorphism.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Support subcategory](support-subcategory.md)
- [Group sequence](../asymptotic/group-sequence.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [The support subcategory is additive](support-dual-additive.md)
- [Duality category of a dual-closed subcategory](../../l-theory/base/categories/dual-subcategory.md)
- [Identity and composite duality functors](../../l-theory/base/categories/duality-functors/composite-duality-functor.md)

## Proof depends on

- [Support ideal](support-ideal.md)
- [Null thickening radii](null-thickening.md)
- [Projection after inclusion](../asymptotic/restriction/inclusion-projection.md)
- [Inclusion after projection](../asymptotic/restriction/projection-inclusion.md)
- [Complementary diagonal projection](../asymptotic/restriction/diagonal-projection-complement.md)
- [Factorization through a diagonal projection, columns](../asymptotic/restriction/diagonal-projection-columns.md)
- [Enumerated indices satisfy the predicate](../asymptotic/restriction/restriction-index-mem.md)
- [Translates and thickenings of an invariant set](thickening-invariant.md)
- [Transposing twice](../asymptotic/structure/transpose-transpose.md)
- [Maps factoring through a dual-closed subcategory form an ideal](../../l-theory/base/categories/filtration-ideal-closure.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
- [Free category of a finite group](../asymptotic/free-category.md)
- [Coordinate inclusion of a restriction](../asymptotic/restriction/coordinate-inclusion.md)
- [Coordinate projection onto a restriction](../asymptotic/restriction/coordinate-projection.md)
- [Diagonal coordinate projection](../asymptotic/restriction/diagonal-projection.md)
- [Enumeration of a sub-basis](../asymptotic/restriction/restriction-index-embedding.md)
- [Restriction to a sub-basis](../asymptotic/restriction/restriction-sub-basis.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [The levelwise transpose](../asymptotic/structure/levelwise-transpose.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
