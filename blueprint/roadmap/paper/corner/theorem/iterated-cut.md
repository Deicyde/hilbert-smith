---
article_id: af_09055d9581d58aeabac4bdfd
declaration: def
origin: bridged
---

# Iterated cut

Take the [standing data](../standing-data.md) and put $X=T\times S^n$. For $1\le m\le n$ let $Z_1=Z=T\times Z_0$ and $Z_m=\varnothing$ for $m\ge2$, and let
$$d_m:\mathbb L_{N-m+1}(\mathcal A_{T\times Y_{m-1}}/\mathcal A_{Z_m})\to\mathbb L_{N-m}(\mathcal A_{T\times Y_m})$$
be the [cut boundary](../../categories/cuts/cut-boundary.md) in $\mathcal A_{\mathbf G}(X)$ for $(T\times A_m,T\times B_m,Z_m)$. The *iterated cut* is
$$\Delta_T=\pi_+\circ d_n\circ q_*\circ d_{n-1}\circ q_*\circ\cdots\circ q_*\circ d_1\circ j_*:\mathbb L_N(\mathcal B_{\mathbf G,Z}(X))\to\mathbb L_4(\mathcal A_{\mathbf G}(T)),$$
where:
- $j:\mathcal B_{\mathbf G,Z}(X)\to\mathcal A_X/\mathcal A_Z$ is the identity-on-objects isomorphism of [exterior quotients](../../categories/supports/exterior-quotient.md);
- each $q:\mathcal A_{T\times Y_m}\to\mathcal A_{T\times Y_m}/\mathcal A_\varnothing$, $1\le m\le n-1$, is the [quotient functor](../../l-theory/base/categories/filtration-quotient.md) for the [support filtration](../../categories/supports/support-filtration.md) of $\varnothing\subseteq T\times Y_m$;
- $\pi_+:\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ is the [component projection](../../evaluation/component-projection.md);
- $j_*$ and $q_*$ are [induced maps](../../l-theory/ultimate/groups/induced-map.md).

The hypotheses of each cut hold. $T\times A_m$, $T\times B_m$ and $Z_m$ are closed ([cut flag](../cut-flag.md), item 1; [the exterior is closed](../exterior-closed.md)) and invariant, because $G_i$ moves only the $T$-coordinate. $Z\subseteq T\times A_1$ and $Z\cap(T\times B_1)=\varnothing$ by [exterior lies in the first cut](../exterior-first-cut.md), and these are trivial for $Z_m=\varnothing$. The union and intersection of the $m$-th cut are $T\times Y_{m-1}$ and $T\times Y_m$ (cut flag, items 2 and 3), and $T\times Y_n=T\times\{y_-,y_+\}$ (cut flag), as $\pi_+$ requires.

This definition rests on the open statement [Lifting](../../l-theory/localization/boundary/lift-to-pair.md), through the cut boundary.

**Remark (not formalized).** The same composite for the trivial group sequence and without $T$ is the [scalar iterated cut](scalar-iterated-cut.md) $\Delta_{\mathbf 1}$, which depends only on $n$, $R$ and $s$. Theorem A uses $\Delta_T$ and $\Delta_{\mathbf 1}$, and Theorem B uses $\Delta_{\mathbf 1}$. The evaluation chapter computes the individual cuts $d_m$ on its labelled models ([formula for the inner cuts](../../evaluation/inner-cut-formula.md)).

## Sources

- HS paper, Section 12.
- New: the cuts are taken along the cube-face flag of the standing data, each one a cut boundary for a closed cover with exterior.

## Depends on

- [Standing data](../standing-data.md)
- [Cut flag](../cut-flag.md)
- [The exterior is closed](../exterior-closed.md)
- [Exterior lies in the first cut](../exterior-first-cut.md)
- [Cut boundary](../../categories/cuts/cut-boundary.md)
- [Exterior quotient](../../categories/supports/exterior-quotient.md)
- [Support filtration](../../categories/supports/support-filtration.md)
- [Quotient by a filtration](../../l-theory/base/categories/filtration-quotient.md)
- [Component projection](../../evaluation/component-projection.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
