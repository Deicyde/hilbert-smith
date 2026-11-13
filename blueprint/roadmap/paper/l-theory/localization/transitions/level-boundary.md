---
article_id: af_aa7e416a5e4de880d7550064
declaration: def
origin: background
statement: formalized
lean: HSP.levelBoundary
---

# Stage boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $j\ge0$. The *stage boundary* is the homomorphism
$$\partial^{(j)}:=\partial\circ t^{\mathrm{im}}:L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)\to L^p_{k+j}(C_{\mathbb Z^{j+1}}\mathcal U),$$
where $t^{\mathrm{im}}$ is the [decorated transition](decorated-transition.md) at stage $j$ and $\partial$ is the [localization boundary](../boundary/localization-boundary.md) of the filtration $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$ ([Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)). The degrees match: $t^{\mathrm{im}}$ goes from $L^p_{k+j}(C_{\mathbb Z^j}(\mathcal A/\mathcal U))$ to $L^{\mathrm{im}}_{k+j+1}$, and $\partial$ lands in $L^p_{k+j}$ of the full subcategory $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$. (The ultimate boundary later carries it on to $L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$ by the duality functor from that full subcategory to $C_{\mathbb Z^{j+1}}(\mathcal U)$ and a transport of degrees.)

This definition rests on the open statement Lifting, through the localization boundary, and, until their proofs are formalized, on the stated results Lifting closed complexes and Independence of the lift (through the localization boundary), Products with the line are decorated (through the decorated transition) and Cobordism is an equivalence relation (through the L-groups).

## Sources

- [Carlsson-Pedersen 1995, §4, boundary on lower L-groups](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the composite.

## Depends on

- [Iterated bounded subcategories](../../bounded/categories/iterated-bounded-sub.md)
- [Lower L-group](lower-l-group.md)
- [The projective L-group](../../base/groups/projective-l-group.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Iterated bounded subcategories are closed under sums and duals](../../bounded/categories/iterated-bounded-sub-additive.md)

## Proof depends on

- [Decorated transition](decorated-transition.md)
- [Localization boundary](../boundary/localization-boundary.md)
- [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)
- [Decorated objects are closed under sums and duals](../decorations/decorated-closure.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)
