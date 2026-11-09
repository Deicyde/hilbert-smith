---
article_id: af_2e67fc43bcc4ff8937c4eab1
declaration: lemma
origin: cited
---

# The half-line comparison

If $K_{-1}(D)=0$, then the [transition map](../localization/line/transition-map.md) $t:L^p_m(D)\to L^p_{m+1}(C_\mathbb ZD)$ (the case $j=0$, $\mathcal A=D$) is bijective.

*Proof sketch.*
1. Decorations. $K_0(\mathrm{Kar}\,C_\mathbb ZD)=K_{-1}(D)=0$ by definition, and $K_0(\mathrm{Kar}\,H_+)=0$ by [$K_0$ of a half-line vanishes](../bounded/half-lines/half-line-k-swindle.md). So for $H_b\subset H_+$ and for $H_-\subset C_\mathbb ZD$ an object $M$ of the completed quotient is decorated iff $[M]=0$, that is, by [Equality in $K_0$](../bounded/categories/k-zero-stable-equality.md), iff $M\oplus X\cong X$ for some object $X$. Additive functors keep such isomorphisms, so $\mathrm{Kar}\,e$ and $\mathrm{Kar}\,\tau$ carry decorated objects to decorated objects. [Equivalence invariance for decorated groups](../localization/sequence/decorated-equivalence-invariance.md), applied to the [inclusion](../bounded/half-lines/half-line-quotient-inclusion.md) $e$ and the [truncation](../bounded/half-lines/half-line-truncation.md) $\tau$ with the unitary data of [Half-line excision](../bounded/half-lines/half-line-excision.md), shows that the [decorated induced map](../localization/sequence/decorated-induced-map.md) $e^{\mathrm{im}}_*$ is an isomorphism.
2. Put $\Phi=\iota_{0*}^{-1}\circ\partial\circ(e^{\mathrm{im}}_*)^{-1}\circ q_*:L^p_{m+1}(C_\mathbb ZD)\to L^p_m(D)$. Here $q_*$ is the [quotient map](../localization/sequence/quotient-map.md) for $H_-\subset C_\mathbb ZD$, $\partial$ is the [localization boundary](../localization/sequence/localization-boundary.md) for $H_b\subset H_+$ ([Bounded support is a Karoubi filtration of a half-line](../bounded/half-lines/bounded-support-filtration.md)), and $\iota_{0*}$ is the isomorphism of [The intersection of the half-lines is $D$](../bounded/half-lines/half-line-intersection.md). $\Phi$ is additive.
3. $\Phi t=\varepsilon_m\,\mathrm{id}$. Let $x\in L^p_m(D)$ and let $y$ be the class of the [image](../localization/sequence/image-pair.md) of the pair of [The truncated line is a pair](truncated-line-pair.md). By [The truncated line computes the quotient image](truncated-line-quotient.md), $e^{\mathrm{im}}_*y=q_*tx$, so $(e^{\mathrm{im}}_*)^{-1}q_*tx=y$. By [the pair formula](../localization/sequence/pair-formula.md), $\partial y$ is the class of the boundary of that pair, which is $\varepsilon_m\iota_{0*}x$ by [The truncated line is a pair](truncated-line-pair.md).
4. Bijective. Injective: $\Phi t=\varepsilon_m\,\mathrm{id}$ with $\varepsilon_m=\pm1$. Surjective: given $z$, put $w=z-\varepsilon_mt\Phi z$. Then $\Phi w=0$, so $\partial(e^{\mathrm{im}}_*)^{-1}q_*w=0$. [Exactness at the quotient](../localization/sequence/exact-at-quotient.md) for $H_b\subset H_+$ and $L^p_{m+1}(H_+)=0$ ([$L^p$ of a half-line vanishes](../bounded/half-lines/half-line-l-swindle.md)) give $q_*w=0$. [Exactness in the middle](../localization/sequence/exact-in-middle.md) for $H_-\subset C_\mathbb ZD$ ([Half-lines are Karoubi filtrations](../bounded/half-lines/half-line-filtration.md)) and $L^p_{m+1}(H_-)=0$ give $w=0$, so $z=t(\varepsilon_m\Phi z)$.

## Sources

- [Ranicki 1992, §16-17](../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Transition map](../localization/line/transition-map.md)
- [Lower $K$-groups](../bounded/categories/lower-k.md)

## Proof depends on

- [$K_0$ of a half-line vanishes](../bounded/half-lines/half-line-k-swindle.md)
- [Equality in $K_0$](../bounded/categories/k-zero-stable-equality.md)
- [Inclusion of the half-line quotient](../bounded/half-lines/half-line-quotient-inclusion.md)
- [Truncation to the positive half-line](../bounded/half-lines/half-line-truncation.md)
- [Half-line excision](../bounded/half-lines/half-line-excision.md)
- [Equivalence invariance for decorated groups](../localization/sequence/decorated-equivalence-invariance.md)
- [Decorated induced map](../localization/sequence/decorated-induced-map.md)
- [Quotient map](../localization/sequence/quotient-map.md)
- [Localization boundary](../localization/sequence/localization-boundary.md)
- [Bounded support is a Karoubi filtration of a half-line](../bounded/half-lines/bounded-support-filtration.md)
- [Half-lines are Karoubi filtrations](../bounded/half-lines/half-line-filtration.md)
- [The intersection of the half-lines is $D$](../bounded/half-lines/half-line-intersection.md)
- [Image of a pair](../localization/sequence/image-pair.md)
- [The truncated line is a pair](truncated-line-pair.md)
- [The truncated line computes the quotient image](truncated-line-quotient.md)
- [Pair formula](../localization/sequence/pair-formula.md)
- [Exactness at the quotient](../localization/sequence/exact-at-quotient.md)
- [Exactness in the middle](../localization/sequence/exact-in-middle.md)
- [$L^p$ of a half-line vanishes](../bounded/half-lines/half-line-l-swindle.md)
