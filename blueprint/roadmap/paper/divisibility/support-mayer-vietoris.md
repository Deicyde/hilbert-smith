---
article_id: af_c7ec5f38a23631fa59204c48
declaration: def
origin: bridged
---

# Support Mayer-Vietoris functor

Let $\mathbf G$ be a group sequence and $X$ a compact metric space with an isometric $C_p$-action. Let $\Lambda_X$ be the lattice of closed $C_p$-invariant subsets of $X$, ordered by inclusion, with $\vee=\cup$ and $\wedge=\cap$. For closed invariant $A,B$ with $S=A\cup B$, let $(\mathcal U_A,\mathcal U_B)$ be the [support excisive pair](../categories/supports/support-excisive-pair.md) in $\mathcal A_S$, with $\mathcal U_Y=\mathcal U_A\cap\mathcal U_B$, a full subcategory of $\mathcal A_S$. Let $j_Y:\mathcal U_Y\to\mathcal A_{A\cap B}$ be the strict duality functor that is the identity on objects and morphisms, which exists by [support intersection](../categories/supports/support-intersection.md). The following data form a [Mayer-Vietoris functor](mayer-vietoris-functor.md) on $\Lambda_X$:
- $F_k(S)=\mathbb L_k(\mathcal A_S)$, where $\mathcal A_S\subset\mathcal A_{\mathbf G}(X)$ is the [support subcategory](../categories/supports/support-subcategory.md);
- $i_{S\le S'}$ is induced by the inclusion $\mathcal A_S\subset\mathcal A_{S'}$;
- $\partial_{A,B}=(j_Y)_*\circ\partial^{\mathrm{exc}}_{A,B}:\mathbb L_k(\mathcal A_{A\cup B})\to\mathbb L_{k-1}(\mathcal U_Y)\to\mathbb L_{k-1}(\mathcal A_{A\cap B})$, with $\partial^{\mathrm{exc}}_{A,B}$ the [excision boundary](../l-theory/ultimate/boundary/excision-boundary.md) of the pair.

*Proof sketch.*
1. The inclusions are strict duality functors, and $\mathcal A_S\subset\mathcal A_S$ is the identity functor while $\mathcal A_S\subset\mathcal A_{S'}\subset\mathcal A_{S''}$ composes to $\mathcal A_S\subset\mathcal A_{S''}$. So $i_{S\le S}=\mathrm{id}$ by [identity on ultimate L](../l-theory/ultimate/groups/induced-map-id.md) and $i_{S'\le S''}i_{S\le S'}=i_{S\le S''}$ by [functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md).
2. $j_Y$ is an isomorphism of duality categories: the functor $\mathcal A_{A\cap B}\to\mathcal U_Y$ that is the identity on objects and morphisms is inverse to it, and both composites are identity functors. So $(j_Y)_*$ is bijective by [equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md), with identity unitary isomorphisms.
3. (Middle exactness.) If $\partial_{A,B}x=0$, then $\partial^{\mathrm{exc}}_{A,B}x=0$ by step 2, so [Mayer-Vietoris middle exactness](../l-theory/ultimate/boundary/mayer-vietoris-middle.md) gives $x=(\iota_A)_*a+(\iota_B)_*b$ with $a\in\mathbb L_k(\mathcal U_A)$, $b\in\mathbb L_k(\mathcal U_B)$ and $\iota_A,\iota_B$ the inclusions into $\mathcal A_S$. Let $j_A:\mathcal U_A\to\mathcal A_A$ and $j_B:\mathcal U_B\to\mathcal A_B$ be the identity on objects and morphisms. Then $\iota_A$ equals the composite of $j_A$ and the inclusion $\mathcal A_A\subset\mathcal A_S$, so by functoriality $x=i_{A\le S}(j_A)_*a+i_{B\le S}(j_B)_*b$.

## Sources

- HS paper, Section 2 (support calculus).
- HS paper, Section 4 (Nilpotence) and Section 6 (Localization boundaries).

## Depends on

- [Mayer-Vietoris functor](mayer-vietoris-functor.md)
- [Group sequence](../categories/asymptotic/group-sequence.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Support excisive pair](../categories/supports/support-excisive-pair.md)
- [Support intersection](../categories/supports/support-intersection.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [Excision boundary](../l-theory/ultimate/boundary/excision-boundary.md)

## Proof depends on

- [Identity on ultimate L](../l-theory/ultimate/groups/induced-map-id.md)
- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Mayer-Vietoris middle exactness](../l-theory/ultimate/boundary/mayer-vietoris-middle.md)
