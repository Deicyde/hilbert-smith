---
article_id: af_ffa69776e1a7aa35cfa2ce92
declaration: lemma
origin: background
---

# Naturality of the ultimate boundary

Let $\mathcal U\subset\mathcal A$ and $\mathcal U'\subset\mathcal A'$ be involution-invariant Karoubi filtrations, $F:\mathcal A\to\mathcal A'$ a duality functor with $F(\mathcal U)\subset\mathcal U'$, and $\bar F:\mathcal A/\mathcal U\to\mathcal A'/\mathcal U'$ the induced functor. Then $\partial'\circ\bar F_*=(F|_{\mathcal U})_*\circ\partial:\mathbb L_k(\mathcal A/\mathcal U)\to\mathbb L_{k-1}(\mathcal U')$.

*Proof sketch.* Every element of the colimit comes from a finite level ([Every element comes from a finite level](../groups/level-exhaustive.md)); take $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$. By [The induced map at each level](../groups/induced-map-level.md) and [The ultimate boundary at each level](ultimate-boundary-level.md),
$\partial'\bar F_*\iota_jx=\sigma_{k,j}\,\iota_{j+1}\,\partial'\big(t^{\mathrm{im}}(C_{\mathbb Z^j}\bar F)_*x\big)$.
By [Naturality of the decorated transition](decorated-transition-naturality.md) this is $\sigma_{k,j}\,\iota_{j+1}\,\partial'(\bar F_{j+1})^{\mathrm{im}}_*t^{\mathrm{im}}x$. [Naturality of the boundary](../../localization/sequence/boundary-naturality.md) for $C_{\mathbb Z^{j+1}}F$, whose restriction to $C_{\mathbb Z^{j+1}}\mathcal U$ is $C_{\mathbb Z^{j+1}}(F|_{\mathcal U})$, turns it into $\sigma_{k,j}\,\iota_{j+1}(C_{\mathbb Z^{j+1}}F|_{\mathcal U})_*\partial^{(j)}x=(F|_{\mathcal U})_*\partial\iota_jx$, again by the two level lemmas.

## Sources

- New: levelwise.

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Every element comes from a finite level](../groups/level-exhaustive.md)
- [The induced map at each level](../groups/induced-map-level.md)
- [The ultimate boundary at each level](ultimate-boundary-level.md)
- [Naturality of the decorated transition](decorated-transition-naturality.md)
- [Naturality of the boundary](../../localization/sequence/boundary-naturality.md)
- [Bounded Karoubi filtrations](../../bounded/categories/bounded-karoubi-filtration.md)
