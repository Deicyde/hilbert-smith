---
article_id: af_a9c754a2c6c7a8990edeb169
declaration: lemma
origin: background
statement: formalized
lean: HSP.UPair.exists_add
---

# Sums of U-pairs

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](../decorations/decorated-object.md), and let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ and $V'=(f':iP'\to D',\delta\phi',i_\%\pi')$ be strict $k$-dimensional [$\mathcal U$-pairs](u-pair.md). There is a strict $k$-dimensional $\mathcal U$-pair $V''$ over $(P'',\pi'')$ with $[qV'']=[qV]+[qV']$ in $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$ and $[P'',\pi'']=[P,\pi]+[P',\pi']$ in $L^p_{k-1}(\mathcal U)$.

*Proof sketch.* By [Sums of pairs](../../base/pairs/sum-of-pairs.md), $V\oplus V'$ is a strict pair with boundary $(iP\oplus iP',i_\%\pi\oplus i_\%\pi')$. Precomposing with the canonical isomorphism $i(P\oplus P')\cong iP\oplus iP'$ ([Pair transport](../../base/pairs/pair-transport.md)) makes it a $\mathcal U$-pair $V''$ over $(P\oplus P',\pi\oplus\pi')$, whose boundary class is $[P,\pi]+[P',\pi']$ by [Group structure on L](../../base/groups/l-group-add.md). The canonical isomorphism $q(D\oplus D')\cong qD\oplus qD'$ carries the structure of $qV''$ to $q_\%\delta\phi\oplus q_\%\delta\phi'$, so [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$ in $\mathrm{Dec}(\mathcal A/\mathcal U)$ gives $[qV'']=[qV]+[qV']$.

## Sources

- New: the additivity step of the localization boundary, split out.

## Depends on

- [U-pairs](u-pair.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Group structure on L](../../base/groups/l-group-add.md)

## Proof depends on

- [Sums of pairs](../../base/pairs/sum-of-pairs.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
