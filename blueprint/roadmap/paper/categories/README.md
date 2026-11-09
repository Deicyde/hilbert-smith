---
article_id: af_271cfad8b5f381569f9fa036
---

# Asymptotic controlled categories

Fix a prime $p$ and a [group sequence](asymptotic/group-sequence.md) $\mathbf G=(G_i,\chi_i)$. Over a compact metric space $X$ with an isometric $C_p$-action, the [asymptotic category](asymptotic/asymptotic-category.md) $\mathcal A_{\mathbf G}(X)$ has as objects sequences of finite free $G_i$-sets with equivariant labels in $X$. Its morphisms are equivariant rational matrices whose [propagation](asymptotic/propagation.md) tends to $0$, taken modulo eventual equality. The propagation bounds for [sums](asymptotic/prop-add.md), [scalar multiples](asymptotic/prop-smul.md) and [products](asymptotic/prop-mul.md) make this a category, and transposition is a [strict duality](asymptotic/asymptotic-duality.md). The control space $T$ of the local-data chapter is one such $X$. Every result here holds for an arbitrary compact metric isometric $C_p$-space, so it applies to $T$, to $T\times S^n$ and to their closed invariant pieces.

A closed invariant $S\subset X$ has its [support subcategory](supports/support-subcategory.md) $\mathcal A_S$. The [support ideal](supports/support-ideal.md) describes, entry by entry, the morphisms that factor through $\mathcal A_S$. From that description come the [Karoubi filtration](supports/support-filtration.md) property, [intersection](supports/support-intersection.md), [excision](supports/excision.md) and [separation](supports/separation.md). Quotienting by an exterior support gives the [exterior quotient](supports/exterior-quotient.md), and a quotient taken in two stages is a single [iterated quotient](supports/iterated-quotient.md).

The functors are as follows. A [relabelling isomorphism](functors/relabelling-isomorphism.md) moves labels by amounts tending to zero. [Pushforward](functors/pushforward.md) composes the labels with an equivariant map, and it gives the [relabelling equivalence](functors/relabelling-equivalence.md) $\mathcal A_{\mathbf G}(S)\simeq\mathcal A_S$. Further functors are [forgetting the group](functors/forget-group.md), the [permutation tensor](functors/tensor-permutation.md) $\tau\otimes-$, and [forgetting labels](functors/forget-labels.md), which lands in the [point category](asymptotic/point-quotient.md) $\mathcal V=\mathcal P/\mathcal S$ (justified by the [point filtration](asymptotic/point-filtration.md)). [Pushforward](functors/push-support.md), [forgetting the group](functors/forget-group-support.md) and the [permutation tensor](functors/tensor-support.md) preserve supports.

The section ends with localization. A closed cover with an exterior gives the [cut square](cuts/cut-square.md), which is the input to the L-theory chapter's [excision compatibility](../l-theory/ultimate/boundary/excision-preimage.md) and [Mayer–Vietoris middle exactness](../l-theory/ultimate/boundary/mayer-vietoris-middle.md). The square defines the [cut boundary](cuts/cut-boundary.md). Its [naturality](cuts/cut-boundary-naturality.md) and the [cut formula](cuts/cut-formula.md) for glued pairs are what the later chapters use.

## Sections

- [The asymptotic category](asymptotic/README.md)
- [Supports and quotients](supports/README.md)
- [Functors](functors/README.md)
- [Cuts](cuts/README.md)

## Sources

- HS paper, Section 2; HS paper, Section 6
