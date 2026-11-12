---
article_id: af_a9c754a2c6c7a8990edeb169
declaration: lemma
origin: background
statement: formalized
lean: HSP.UPair.exists_add
proof: formalized
---

# Sums of U-pairs

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](../decorations/decorated-object.md), and let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ and $V'=(f':iP'\to D',\delta\phi',i_\%\pi')$ be strict $k$-dimensional [$\mathcal U$-pairs](u-pair.md). There is a strict $k$-dimensional $\mathcal U$-pair $V''$ over $(P'',\pi'')$ with $[qV'']=[qV]+[qV']$ in $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ and $[P'',\pi'']=[P,\pi]+[P',\pi']$ in $L^p_{k-1}(\mathcal U)$.

*Proof sketch.* By [Sums of pairs](../../base/pairs/sum-of-pairs.md), $V\oplus V'$ is a strict pair with boundary $(iP\oplus iP',i_\%\pi\oplus i_\%\pi')$. Precomposing with the canonical isomorphism $i(P\oplus P')\cong iP\oplus iP'$, which carries $i_\%(\pi\oplus\pi')$ to $i_\%\pi\oplus i_\%\pi'$ ([Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)), gives by [Pair transport](../../base/pairs/pair-transport.md) a $\mathcal U$-pair $V''$ over $(P\oplus P',\pi\oplus\pi')$, whose boundary class is $[P,\pi]+[P',\pi']$ by [Group structure on L](../../base/groups/l-group-add.md). Its codomain is $D\oplus D'$ with structure $\delta\phi\oplus\delta\phi'$, so the canonical isomorphism $q(D\oplus D')\cong qD\oplus qD'$ carries the structure $q_\%(\delta\phi\oplus\delta\phi')$ of $qV''$ to $q_\%\delta\phi\oplus q_\%\delta\phi'$, by the same lemma. All chain objects involved are decorated, so [Sums in a full subcategory](../decorations/subcategory-sum.md) gives $[qV'']=[qV]+[qV']$.

## Sources

- New: the additivity step of the localization boundary, split out.

## Depends on

- [U-pairs](u-pair.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [The projective L-group](../../base/groups/projective-l-group.md)

## Proof depends on

- [Sums of pairs](../../base/pairs/sum-of-pairs.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Duality functors preserve sums of structures](../../base/complexes/functors/functor-structure-sum.md)
- [Sums in a full subcategory](../decorations/subcategory-sum.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [The sum of two Poincaré complexes](../../base/pairs/poincare-sum.md)
- [Sum of structured complexes](../../base/complexes/sum-of-complexes.md)
