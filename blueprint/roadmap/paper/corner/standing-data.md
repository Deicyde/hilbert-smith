---
article_id: af_b02080be1c6eb585871a5846
declaration: def
origin: bridged
---

# Standing data

The standing data consist of:
- a prime $p$, with $C_p=\mathbb Z/p$ written additively;
- a [group sequence](../categories/asymptotic/group-sequence.md) $\mathbf G=(G_i,\chi_i)$ with $G_i=\mathbb Z/p^{a_i}$ for integers $a_i\ge1$, written additively, and $\chi_i:G_i\to C_p$ surjective; put $q_i=|G_i|$;
- a nonempty compact metric space $(T,d_T)$ with an isometric $C_p$-action $(c,t)\mapsto c\cdot t$ that is free: $c\cdot t=t$ implies $c=0$;
- an integer $n\ge1$ and reals $R>0$ and $s$ with $0<s<R/\sqrt n$.

Put $N=n+4$. The following are defined from these data.
1. $S^n=\mathbb R^n\cup\{\infty\}$, with $|z|$ the Euclidean norm on $\mathbb R^n$. The *round metric* $d_S(z,w)$ is the angle between $\sigma^{-1}(z)$ and $\sigma^{-1}(w)$, where $\sigma$ is stereographic projection from $(0,\dots,0,1)$ of the unit sphere of $\mathbb R^{n+1}$ onto $S^n$.
2. The exterior $Z_0=\{\infty\}\cup\{z\in\mathbb R^n:|z|\ge R\}\subseteq S^n$ and $Z=T\times Z_0\subseteq T\times S^n$. The product $T\times S^n$ has the maximum metric $\max(d_T,d_S)$, and $G_i$ acts on it by $g\cdot(t,z)=(\chi_i(g)\cdot t,z)$.
3. The cut sets: for $1\le m\le n$,
   - $B_m=[-s,s]^{n-m+1}\times\{s\}^{m-1}\subseteq\mathbb R^n$;
   - $Y_m=\{x\in B_m:|x_k|=s\text{ for some }k\le n-m+1\}$, the boundary of $B_m$ in the affine plane $\mathbb R^{n-m+1}\times\{s\}^{m-1}$;
   - $Y_0=S^n$ and $A_m=\overline{Y_{m-1}\setminus B_m}$, the closure in $S^n$;
   - $y_\pm=(\pm s,s,\dots,s)$.

The properties of the cut sets that the iterated cut uses are the [cut flag](cut-flag.md) and the [exterior lies in the first cut](exterior-first-cut.md).

**Remark (not formalized).** In the proof of the main theorem, $T$ is the [control space](../local-data/control/control-space.md) with the [orbit metric](../local-data/control/control-metric.md), which is a [compact metric space](../local-data/control/control-metric-properties.md), with the [cyclic action](../local-data/control/control-action.md), which is [free](../local-data/control/control-action-free.md) and [isometric](../local-data/control/control-action-isometric.md); $R$ is the buffer radius of the [fixed local data](../local-data/control/fixed-local-data.md); and $G_i=\mathbb Z/p^i$ with $\chi_i$ reduction modulo $p$.

## Sources

- HS paper, Sections 2, 8 and 12.
- New: $T$ is an arbitrary nonempty compact free isometric $C_p$-space rather than the detector sphere, and the cut sets are faces of a cube rather than a ball and hemisphere flag.

## Depends on

- [Group sequence](../categories/asymptotic/group-sequence.md)
