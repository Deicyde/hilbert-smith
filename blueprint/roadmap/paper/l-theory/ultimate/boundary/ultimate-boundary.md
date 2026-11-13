---
article_id: af_723f83ce92dedcbb8d75baf1
declaration: def
origin: cited
statement: formalized
lean: HSP.ultBoundary
---

# Ultimate boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. $\partial:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal U)$ is the homomorphism out of the colimit given at stage $j$ by
$$x\longmapsto\iota_{j+1}\big(\rho_j\,\partial^{(j)}x\big),\qquad x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U),$$
where $\partial^{(j)}:L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)\to L^p_{k+j}(C_{\mathbb Z^{j+1}}\mathcal U)$ is the [stage boundary](../../localization/transitions/level-boundary.md), with values in $L^p_{k+j}$ of the full subcategory $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$, and
$$\rho_j:L^p_{k+j}(C_{\mathbb Z^{j+1}}\mathcal U)\to L^p_{(k-1)+(j+1)}\big(C_{\mathbb Z^{j+1}}(\mathcal U)\big)=L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$$
is the [homomorphism induced](../../base/groups/induced-map.md) by the duality functor $C_{\mathbb Z^{j+1}}\mathcal U\to C_{\mathbb Z^{j+1}}(\mathcal U)$ of [Iterated bounded categories of a subcategory](sub-pow-identification.md), followed by the [transport of L-groups](../../base/groups/l-group-cast.md) along $k+j=(k-1)+(j+1)$, as in [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md). The colimit maps $\iota_j$ are the [stage maps](../groups/ultimate-stage-map.md) of the [sequence of lower L-groups](../groups/lower-l-sequence.md). These maps are compatible with $t$: by [Stages are compatible with the transition](../groups/level-compatible.md) and [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md),
$$\iota_{j+1}\rho_j\partial^{(j)}x=\iota_{j+2}\,t\,\rho_j\partial^{(j)}x=\iota_{j+2}\,\rho_{j+1}\partial^{(j+1)}tx.$$

This definition rests on the open statement Lifting, through the stage boundaries, and, until their proofs are formalized, on the stated results [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md) (which its compatibility with $t$ uses) and, through the stage boundaries, Lifting closed complexes and Independence of the lift (through the localization boundary), Products with the line are decorated (through the decorated transition) and Cobordism is an equivalence relation (through the L-groups).

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level boundary](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the group-level colimit of the stage boundaries.

## Depends on

- [Ultimate L-group](../groups/ultimate-l-group.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)

## Proof depends on

- [Stage boundary](../../localization/transitions/level-boundary.md)
- [Transition commutes with the boundary](../../localization/transitions/transition-boundary-commute.md)
- [Stages are compatible with the transition](../groups/level-compatible.md)
- [Iterated bounded categories of a subcategory](sub-pow-identification.md)
- [Stage maps into the ultimate L-group](../groups/ultimate-stage-map.md)
- [Sequence of lower L-groups](../groups/lower-l-sequence.md)
- [Transport of L-groups along an equality of degrees](../../base/groups/l-group-cast.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Lower transition map](../../localization/transitions/transition-lower.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Lower L-group](../../localization/transitions/lower-l-group.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [L-group](../../base/groups/l-group.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Iterated transition](../groups/transition-iter.md)
