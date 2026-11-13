---
article_id: af_8e4160d96cfba8f2d33a3dcf
declaration: lemma
origin: cited
statement: formalized
lean: HSP.UPair.mk_P_eq_of_image
---

# Independence of the lift

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration, and let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ and $V'=(f':iP'\to D',\delta\phi',i_\%\pi')$ be strict $k$-dimensional [$\mathcal U$-pairs](u-pair.md) with $[qV]=[qV']$ in $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$. Then $[P,\pi]=[P',\pi']$ in $L^p_{k-1}(\mathcal U)$.

*Proof sketch.* (1) Negating $(\delta\phi',i_\%\pi')$ gives a $\mathcal U$-pair $-V'$ over $(P',-\pi')$ ([Pair transport](../../base/pairs/pair-transport.md)). By [Sums of pairs](../../base/pairs/sum-of-pairs.md), $V\oplus(-V')$ is a strict pair with boundary $(iP\oplus iP',i_\%\pi\oplus(-i_\%\pi'))$. Precomposing with the canonical isomorphism $i(P\oplus P')\cong iP\oplus iP'$ makes it a $\mathcal U$-pair $V''$ over $(P\oplus P',\pi\oplus(-\pi'))$. (2) The canonical isomorphism $q(D\oplus D')\cong qD\oplus qD'$ carries the structure of $qV''$ to $q_\%\delta\phi\oplus(-q_\%\delta\phi')$. By [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$, [Group structure on L](../../base/groups/l-group-add.md) and [Negation in L](../../base/groups/l-group-neg.md), all in $\mathrm{Dec}(\mathcal A/\mathcal U)$, $[qV'']=[qV]-[qV']=0$. (3) By [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md) in $\mathrm{Dec}(\mathcal A/\mathcal U)$, $qV''$ is the boundary of a strict $(k+1)$-dimensional pair $W$ in $\mathrm{Dec}(\mathcal A/\mathcal U)$. (4) Part (a) of [Lifting](lift-to-pair.md) for $V''$ and $W$ gives a strict pair in $\mathrm{Kar}\,\mathcal U$ with boundary $(P\oplus P',(-\pi)\oplus\pi')$. By [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md), the group structure and negation in $L^p_{k-1}(\mathcal U)$, $-[P,\pi]+[P',\pi']=0$.

## Sources

- New: group-level arrangement of [Carlsson-Pedersen 1995, Theorem 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [U-pairs](u-pair.md)
- [Image of a pair with boundary in Kar U](image-pair.md)
- [L-group](../../base/groups/l-group.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Decorated objects are closed under sums and duals](../decorations/decorated-closure.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)

## Proof depends on

- [Pair transport](../../base/pairs/pair-transport.md)
- [Sums of pairs](../../base/pairs/sum-of-pairs.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Negation in L](../../base/groups/l-group-neg.md)
- [Zero classes bound](../../base/groups/l-group-zero-iff-bounds.md)
- [Lifting](lift-to-pair.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
