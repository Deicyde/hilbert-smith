---
article_id: af_04f0beb6ade57df21bba8a0f
declaration: lemma
origin: background
statement: formalized
lean: HSP.transitionLower_levelBoundary
---

# Transition commutes with the boundary

Let $\mathcal U\subset\mathcal A$ be an involution-invariant Karoubi filtration. For $j\ge0$ and $x\in L^{\langle -j\rangle}_k(\mathcal A/\mathcal U)$,
$$t\big(\partial^{(j)}x\big)=\partial^{(j+1)}(t\,x)\quad\text{in }L^{\langle -j-2\rangle}_{k-1}(\mathcal U),$$
where $\partial^{(j)}$ is the [stage boundary](level-boundary.md), on the left $t$ is the [lower transition map](transition-lower.md) of $\mathcal U$ at stage $j+1$, and on the right that of $\mathcal A/\mathcal U$ at stage $j$. Here $\partial^{(j)}x$, an element of $L^p_{k+j}$ of the full subcategory $C_{\mathbb Z^{j+1}}\mathcal U\subset C_{\mathbb Z^{j+1}}\mathcal A$, is read in $L^{\langle -j-1\rangle}_{k-1}(\mathcal U)$ through the identification of [Iterated bounded categories of a subcategory](../../ultimate/boundary/sub-pow-identification.md). This identification is followed by the [transport of L-groups](../../base/groups/l-group-cast.md) along $k+j=(k-1)+(j+1)$.

*Proof sketch.* Write $\mathcal U_n=C_{\mathbb Z^n}\mathcal U\subset C_{\mathbb Z^n}\mathcal A$, an involution-invariant Karoubi filtration ([Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)).
1. Lift. By [Lifting closed complexes](../boundary/lift-to-pair-closed.md) for $\mathcal U_{j+1}$, there is a strict $(k+j+1)$-dimensional $\mathcal U_{j+1}$-[pair](../boundary/u-pair.md) $V$ over $(P,\pi)$ with $[qV]=t^{\mathrm{im}}x$, where $qV$ is its [image](../boundary/image-pair.md). By the [pair formula](../boundary/pair-formula.md), $\partial^{(j)}x=\partial\,t^{\mathrm{im}}x=[P,\pi]$.
2. Product. By [Decorated transition of an image pair](image-pair-transition.md) with $n=j+1$, $V\otimes\Lambda$ is a strict $(k+j+2)$-dimensional $\mathcal U_{j+2}$-pair over $(P\otimes\Lambda,\pi\otimes\lambda)$, with $[q(V\otimes\Lambda)]=t^{\mathrm{im}}\big((e_{j+1})_*\,\mathrm{fgt}\,[qV]\big)$.
3. By [Forgetting after the decorated transition](transition-quotient.md), $(e_{j+1})_*\,\mathrm{fgt}\,[qV]=(e_{j+1})_*\,\mathrm{fgt}\,t^{\mathrm{im}}x=t\,x$. So $[q(V\otimes\Lambda)]=t^{\mathrm{im}}(t\,x)$.
4. By the [pair formula](../boundary/pair-formula.md) again, $\partial^{(j+1)}(t\,x)=\partial\,t^{\mathrm{im}}(t\,x)=[P\otimes\Lambda,\pi\otimes\lambda]=t[P,\pi]=t\big(\partial^{(j)}x\big)$.

**Remark (not formalized).** No sign appears because the boundary of the product of a pair with the line, the line being the second factor, is the product of the boundary with the line ([Product of a pair with the line](../products/product-with-line.md)).

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md); [Carlsson-Pedersen 1995, §4](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: a lift of $t^{\mathrm{im}}x$ times the line, read off with the pair formula.

## Depends on

- [Stage boundary](level-boundary.md)
- [Lower transition map](transition-lower.md)
- [Iterated bounded categories of a subcategory](../../ultimate/boundary/sub-pow-identification.md)
- [Transport of L-groups along an equality of degrees](../../base/groups/l-group-cast.md)
- [The projective L-group](../../base/groups/projective-l-group.md)

## Proof depends on

- [Lifting closed complexes](../boundary/lift-to-pair-closed.md)
- [U-pairs](../boundary/u-pair.md)
- [Image of a pair with boundary in Kar U](../boundary/image-pair.md)
- [Pair formula](../boundary/pair-formula.md)
- [Decorated transition of an image pair](image-pair-transition.md)
- [Forgetting after the decorated transition](transition-quotient.md)
- [Iterated bounded filtrations](../../bounded/categories/iterated-bounded-filtration.md)
- [Iterated bounded quotients](../../bounded/categories/iterated-bounded-quotient.md)
