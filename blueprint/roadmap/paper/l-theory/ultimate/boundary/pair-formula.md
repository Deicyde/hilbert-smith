---
article_id: af_081f9a2fd218001c83ea8ff0
declaration: lemma
origin: bridged
---

# Ultimate pair formula

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration and $V$ a strict $k$-dimensional [$\mathcal U$-pair](../../localization/boundary/u-pair.md) over $(P,\pi)$, with [image](../../localization/boundary/image-pair.md) $qV$. Then
$$\partial\,\mathrm{cls}\big(\mathrm{fgt}\,[qV]\big)=\mathrm{cls}[P,\pi]\quad\text{in }\mathbb L_{k-1}(\mathcal U),$$
where $\mathrm{fgt}$ [forgets the decoration](../../localization/decorations/forget-decoration.md) and $\partial$ is the [ultimate boundary](ultimate-boundary.md).

*Proof sketch.* Put $x=\mathrm{fgt}[qV]\in L^{\langle 0\rangle}_k(\mathcal A/\mathcal U)$.
1. By [The ultimate boundary at each stage](ultimate-boundary-level.md) with $j=0$, $\partial\,\mathrm{cls}\,x=\iota_1\,\partial(t^{\mathrm{im}}x)$.
2. By [Decorated transition of an image pair](../../localization/transitions/image-pair-transition.md) with $n=0$ (where $e_0=\mathrm{id}$), $V\otimes\Lambda$ is a strict $(k+1)$-dimensional $C_\mathbb Z\mathcal U$-pair over $(P\otimes\Lambda,\pi\otimes\lambda)$ with $[q_1(V\otimes\Lambda)]=t^{\mathrm{im}}x$.
3. The [pair formula](../../localization/boundary/pair-formula.md) for $C_\mathbb Z\mathcal U\subset C_\mathbb Z\mathcal A$ gives $\partial(t^{\mathrm{im}}x)=[P\otimes\Lambda,\pi\otimes\lambda]=t[P,\pi]$, by the definition of the [transition map](../../localization/transitions/transition-map.md).
4. So $\partial\,\mathrm{cls}\,x=\iota_1t[P,\pi]=\iota_0[P,\pi]=\mathrm{cls}[P,\pi]$ by [Stages are compatible with the transition](../groups/level-compatible.md).

## Sources

- HS paper, Section 6 (the boundary of a relative-pair representative is its boundary, with sign $+1$)
- [Carlsson-Pedersen 1995, proof of Thm 4.1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Ultimate boundary](ultimate-boundary.md)
- [U-pairs](../../localization/boundary/u-pair.md)
- [Image of a pair with boundary in Kar U](../../localization/boundary/image-pair.md)
- [Forgetting the decoration](../../localization/decorations/forget-decoration.md)

## Proof depends on

- [The ultimate boundary at each stage](ultimate-boundary-level.md)
- [Decorated transition of an image pair](../../localization/transitions/image-pair-transition.md)
- [Pair formula](../../localization/boundary/pair-formula.md)
- [Transition map](../../localization/transitions/transition-map.md)
- [Stages are compatible with the transition](../groups/level-compatible.md)
