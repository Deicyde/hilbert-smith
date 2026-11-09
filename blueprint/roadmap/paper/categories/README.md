---
---

# Asymptotic controlled categories

Fix a prime $p$ and a [group sequence](group-sequence.md) $\mathbf G=(G_i,\chi_i)$. Over a compact metric space $X$ with an isometric $C_p$-action, the [asymptotic category](asymptotic-category.md) $\mathcal A_{\mathbf G}(X)$ has as objects sequences of finite free $G_i$-sets with equivariant labels in $X$. Its morphisms are equivariant rational matrices whose [propagation](propagation.md) tends to $0$, taken modulo eventual equality. The [propagation bounds](propagation-bounds.md) make this a category, and transposition is a [strict duality](asymptotic-duality.md). The control space $T$ of the local-data chapter is one such $X$. Every result here holds for an arbitrary compact metric isometric $C_p$-space, so it applies to $T$, to $T\times S^n$ and to their closed invariant pieces.

A closed invariant $S\subset X$ has its [support subcategory](support-subcategory.md) $\mathcal A_S$. The [support ideal](support-ideal.md) describes, entry by entry, the morphisms that factor through $\mathcal A_S$. From that description come the [Karoubi filtration](support-filtration.md) property, [intersection](support-intersection.md), [excision](excision.md) and [separation](separation.md). Quotienting by an exterior support gives the [exterior quotient](exterior-quotient.md), and a quotient taken in two stages is a single [iterated quotient](iterated-quotient.md).

The functors are as follows. A [relabelling isomorphism](relabelling-isomorphism.md) moves labels by amounts tending to zero. [Pushforward](pushforward.md) composes the labels with an equivariant map, and it gives the [relabelling equivalence](relabelling-equivalence.md) $\mathcal A_{\mathbf G}(S)\simeq\mathcal A_S$. Further functors are [forgetting the group](forget-group.md), the [permutation tensor](tensor-permutation.md) $\tau\otimes-$, and [forgetting labels](forget-labels.md), which lands in the [point categories](point-categories.md) $\mathcal V=\mathcal P/\mathcal S$ (justified by the [point filtration](point-filtration.md)). [Support preservation](support-preservation.md) records which supports each functor respects.

The section ends with localization. A closed cover with an exterior gives the [cut square](cut-square.md), which is the input to the L-theory chapter's [excision compatibility](../l-theory/D8.md) and [Mayer–Vietoris middle exactness](../l-theory/D9.md). The square defines the [cut boundary](cut-boundary.md). Its [naturality](cut-boundary-naturality.md) and the [cut formula](cut-formula.md) for glued pairs are what the later chapters use.

## Sources

- HS paper, Section 2; HS paper, Section 6
