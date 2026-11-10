---
article_id: af_4fa7c7bff03cb4fc8566d697
declaration: def
origin: bridged
---

# The endomorphism $\nu$

On the [support Mayer-Vietoris functor](support-mayer-vietoris.md), put $\nu_S=p\cdot\mathrm{id}-(\tau_S)_*$ on $\mathbb L_k(\mathcal A_S)$, where $\tau_S:\mathcal A_S\to\mathcal A_S$ is the restriction of the [permutation tensor](../categories/functors/tensor-permutation.md) $\tau\otimes-$, which [preserves supports](../categories/functors/tensor-support.md). This family is a [natural endomorphism](natural-endomorphism.md).

*Proof sketch.*
1. For $S\le S'$, $\tau_{S'}$ composed with the inclusion $\mathcal A_S\subset\mathcal A_{S'}$ equals the inclusion composed with $\tau_S$, as strict duality functors. By [functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md), $(\tau_{S'})_*i_{S\le S'}=i_{S\le S'}(\tau_S)_*$.
2. For $A,B$ with $S=A\cup B$, $\tau_S$ carries $\mathcal U_A$ into $\mathcal U_A$ and $\mathcal U_B$ into $\mathcal U_B$ by [support preservation](../categories/functors/tensor-support.md). [Naturality of the excision boundary](../l-theory/ultimate/boundary/excision-boundary-naturality.md) gives $\partial^{\mathrm{exc}}_{A,B}(\tau_S)_*=(\tau_S|_{\mathcal U_Y})_*\partial^{\mathrm{exc}}_{A,B}$. Since $j_Y\circ\tau_S|_{\mathcal U_Y}=\tau_{A\cap B}\circ j_Y$ strictly, functoriality gives $\partial_{A,B}(\tau_S)_*=(\tau_{A\cap B})_*\partial_{A,B}$.
3. Both $p\cdot\mathrm{id}$ and $(\tau)_*$ are additive and commute with $i$ and $\partial$, so their difference does too.

## Sources

- HS paper, Section 4.

## Depends on

- [Support Mayer-Vietoris functor](support-mayer-vietoris.md)
- [Natural endomorphism](natural-endomorphism.md)
- [Permutation tensor](../categories/functors/tensor-permutation.md)
- [Permutation tensor preserves support](../categories/functors/tensor-support.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)

## Proof depends on

- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
- [Naturality of the excision boundary](../l-theory/ultimate/boundary/excision-boundary-naturality.md)
