---
article_id: af_2bebaf05c4ddf6ed3c093e94
declaration: theorem
origin: cited
---

# Boundary then inclusion vanishes

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration with inclusion $i:\mathcal U\to\mathcal A$. Then $i_*\circ\partial=0:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal A)$.

*Proof sketch.* Every element of the colimit comes from a finite level ([Every element comes from a finite level](../groups/level-exhaustive.md)); take $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$. By [The ultimate boundary at each level](ultimate-boundary-level.md) and [The induced map at each level](../groups/induced-map-level.md), $i_*\partial\iota_jx=\iota_{j+1}(C_{\mathbb Z^{j+1}}i)_*\partial(t^{\mathrm{im}}x)$. Here $C_{\mathbb Z^{j+1}}i$ is the inclusion of the Karoubi filtration $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$ ([Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)), so [Boundary then inclusion is zero](../../localization/boundary/boundary-composite-zero.md) gives $0$.

## Sources

- [Carlsson-Pedersen 1995, Thm 4.2, spectrum-level statement](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: group-level reduction to the finite level.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [The induced map at each level](../groups/induced-map-level.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
- [Boundary then inclusion is zero](../../localization/boundary/boundary-composite-zero.md)
