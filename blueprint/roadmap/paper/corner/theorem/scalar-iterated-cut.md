---
article_id: af_87aaf4d61581a062daba23da
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.scalarIteratedCut
---

# Scalar iterated cut

Let $p$ be a prime, $n\ge1$, $R>0$ and $0<s<R/\sqrt n$, and put $N=n+4$. Take the [exterior](../exterior.md) $Z_0\subseteq S^n$ and the [cut sets](../cut-sets.md), and work in $\mathcal A_{\mathbf 1}(S^n)$ for the [trivial group sequence](../../categories/asymptotic/trivial-group-sequence.md) $\mathbf 1$ of the prime $p$, so that $\Delta_{\mathbf 1}$ depends on $p$ as well as on $n$, $R$ and $s$. For $1\le m\le n$ let $Z^0_1=Z_0$ and $Z^0_m=\varnothing$ for $m\ge2$, and let
$$d_m:\mathbb L_{N-m+1}(\mathcal A_{Y_{m-1}}/\mathcal A_{Z^0_m})\to\mathbb L_{N-m}(\mathcal A_{Y_m})$$
be the [cut boundary](../../categories/cuts/cut-boundary.md) for $(A_m,B_m,Z^0_m)$. The *scalar iterated cut* is
$$\Delta_{\mathbf 1}=\pi_+\circ d_n\circ q_*\circ d_{n-1}\circ q_*\circ\cdots\circ q_*\circ d_1\circ j_*:\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n))\to\mathbb L_4(\mathcal V_{\mathbf 1}),$$
where:
- $j=j_{Z_0}:\mathcal B_{\mathbf 1,Z_0}(S^n)\to\mathcal A_{S^n}/\mathcal A_{Z_0}$ is the [exterior quotient as a cut domain](../../categories/cuts/exterior-cut-identification.md), from the [exterior quotient](../../categories/supports/exterior-quotient.md) to the domain of $d_1$ (here $Y_0=S^n$);
- each $q:\mathcal A_{Y_m}\to\mathcal A_{Y_m}/\mathcal A_\varnothing$, $1\le m\le n-1$, is the quotient functor for the support filtration of $\varnothing\subseteq Y_m$, from the target of $d_m$ to the domain of $d_{m+1}$;
- $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$ is the [scalar component projection](../../evaluation/scalar-component-projection.md) for $n$ and $s$;
- $j_*$ and $q_*$ are [induced maps](../../l-theory/ultimate/groups/induced-map.md).

The hypotheses of each cut hold. $A_m$ and $B_m$ are closed ([cut flag](../cut-flag.md), item 1), $Z_0$ is closed ([the exterior is closed](../exterior-closed.md)), and all are invariant because the group acts trivially on $S^n$. $Z_0\cap B_1=\varnothing$ ([the exterior lies in the first cut](../exterior-first-cut.md)), and this is trivial for $Z^0_m=\varnothing$. The union and intersection of the $m$-th cut are $Y_{m-1}$ and $Y_m$ (cut flag, items 2 and 3), and $Y_n=\{y_-,y_+\}$ with $y_-\ne y_+$ (cut flag), as $\pi_+$ requires; $\pi_+$ needs only $n\ge1$ and $s>0$.

This definition rests on the open statement Lifting, through the cut boundary and the ultimate boundary it is built from, and, until their proofs are formalized, on the stated results Transition commutes with the boundary (through the ultimate boundary), Lifting closed complexes and Independence of the lift (through the localization boundary), Products with the line are decorated (through the decorated transition), Cobordism is an equivalence relation (through the L-groups) and Naturality of the transition (through the induced maps on ultimate L-groups).

**Remark (not formalized).** Support-preserving functors commute strictly with the connecting functors: with each $q$ by the induced functor on support quotients, and with $j$ by the naturality of the exterior quotient as a cut domain. Besides $p$, $\Delta_{\mathbf 1}$ depends only on $n$, $R$ and $s$: no other group sequence and no control space enters. Theorem A uses it with the $p$, $n$, $R$, $s$ of its standing data, and Theorem B uses it for any $p$, $n$, $R$, $s$ as above, including the case of an empty control space in the final proof.

## Sources

- HS paper, Section 12.
- New: the cuts are taken along the cube-face flag, each one a cut boundary for a closed cover with exterior.

## Depends on

- [The trivial group sequence](../../categories/asymptotic/trivial-group-sequence.md)
- [The exterior](../exterior.md)
- [Exterior quotient](../../categories/supports/exterior-quotient.md)
- [Point category](../../categories/asymptotic/point-quotient.md)
- [The round sphere](../round-sphere.md)
- [Ultimate L-group](../../l-theory/ultimate/groups/ultimate-l-group.md)

## Proof depends on

- [The cut sets](../cut-sets.md)
- [The exterior is closed](../exterior-closed.md)
- [Cut flag](../cut-flag.md)
- [Exterior lies in the first cut](../exterior-first-cut.md)
- [Cut boundary](../../categories/cuts/cut-boundary.md)
- [The exterior quotient as a cut domain](../../categories/cuts/exterior-cut-identification.md)
- [Scalar component projection](../../evaluation/scalar-component-projection.md)
- [Induced map on ultimate L](../../l-theory/ultimate/groups/induced-map.md)
- [Asymptotic category](../../categories/asymptotic/asymptotic-category.md)
- [Support subcategory inside a support subcategory](../../categories/supports/relative-support.md)
- [Support subcategory](../../categories/supports/support-subcategory.md)
- [The boundary of the cube face](../cut-face-boundary.md)
- [The cube face](../cut-face.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [The quotient duality functor](../../l-theory/base/categories/quotient-duality-functor.md)
