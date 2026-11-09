---
article_id: af_e27cb5f1acde64163b6a0a77
declaration: lemma
origin: bridged
---

# A union modulo one side

Let $\mathcal U_B\subset\mathcal A$ be an involution-invariant Karoubi filtration with quotient functor $q_B$. Let $V_A=(h_A:C\to D_A,\delta\phi_A,\phi)$ and $V_B=(h_B:C\to D_B,\delta\phi_B,-\phi)$ be strict $k$-dimensional symmetric Poincaré pairs in $\mathrm{Kar}\,\mathcal A$ with $C$ and $D_B$ in $\mathrm{Kar}\,\mathcal U_B$, and let $(U,\Phi)=V_A\cup_CV_B$ be their closed union. Then
$$(q_B)_*[U,\Phi]=\mathrm{forget}\,[\operatorname{im}V_A]\quad\text{in }L^p_k(\mathcal A/\mathcal U_B).$$

*Proof sketch.* $(U,\Phi)$ is a strict Poincaré complex by [Closed gluing](../../base/pairs/gluing-closed.md), with $U_r=D_{A,r}\oplus D_{B,r}\oplus C_{r-1}$ ([Algebraic union](../../base/pairs/algebraic-union.md)).
1. By [Kernel of the completed quotient](../../base/categories/karoubi-quotient-kernel.md), the identities of $D_{B,r}$ and $C_{r-1}$ map to $0$ in $\mathrm{Kar}(\mathcal A/\mathcal U_B)$, so these summands become zero objects, and the images of $h_A$ and $h_B$ are $0$.
2. Hence the projection $\pi:q_BU\to q_BD_A$ is an isomorphism of chain complexes in $\mathrm{Kar}(\mathcal A/\mathcal U_B)$. Every entry of $\Phi$ other than $\delta\phi_A$ has its row or its column in $D_B$ or $C$, so $\pi_\%(q_B)_\%\Phi$ is the image of $\delta\phi_A$, which is the structure of $\operatorname{im}V_A$ ([Image of a pair](../../localization/sequence/image-pair.md)).
3. [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $h=\pi$ and $\chi=0$ gives the equality; the right side is unchanged by [forgetting the decoration](../../localization/sequence/forget-decoration.md) as a representative.

## Sources

- HS paper, Section 6 (modulo one side of the cover, the other side, the common boundary and the interface corrections vanish)
- New: the explicit projection and its effect on the union structure.

## Depends on

- [Algebraic union](../../base/pairs/algebraic-union.md)
- [Image of a pair](../../localization/sequence/image-pair.md)
- [Forgetting the decoration](../../localization/sequence/forget-decoration.md)
- [Induced homomorphism](../../base/groups/induced-map.md)

## Proof depends on

- [Closed gluing](../../base/pairs/gluing-closed.md)
- [Kernel of the completed quotient](../../base/categories/karoubi-quotient-kernel.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
