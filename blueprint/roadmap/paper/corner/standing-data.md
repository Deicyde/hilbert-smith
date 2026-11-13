---
article_id: af_b02080be1c6eb585871a5846
declaration: structure
origin: bridged
statement: formalized
lean: HSP.Corner.StandingData
---

# Standing data

The standing data consist of:
- a prime $p$, with $C_p=\mathbb Z/p$ written additively;
- a [group sequence](../categories/asymptotic/group-sequence.md) $\mathbf G=(G_i,\chi_i)$ with $G_i=\mathbb Z/p^{a_i}$ for integers $a_i\ge1$, written additively, and $\chi_i:G_i\to C_p$ surjective; put $q_i=|G_i|$;
- a nonempty compact metric space $(T,d_T)$ with an isometric $C_p$-action $(c,t)\mapsto c\cdot t$ that is free: $c\cdot t=t$ implies $c=0$;
- an integer $n\ge1$ and reals $R>0$ and $s$ with $0<s<R/\sqrt n$.

Put $N=n+4$. The standing data use the following definitions, which need only part of the data:
1. the [round sphere](round-sphere.md) $(S^n,d_S)$, from $n$;
2. the [exterior](exterior.md) $Z_0\subseteq S^n$, from $n$ and $R$, and $Z=T\times Z_0\subseteq T\times S^n$, where $T\times S^n$ has the maximum metric $\max(d_T,d_S)$; here $G_i$ acts on $T\times S^n$ by $g\cdot(t,z)=(\chi_i(g)\cdot t,z)$;
3. the [cut sets](cut-sets.md) $B_m,Y_m,A_m$ ($1\le m\le n$), $Y_0=S^n$ and $y_\pm$, from $n$ and $s$.

The properties of these sets that the iterated cut uses are [the exterior is closed](exterior-closed.md), the [cut flag](cut-flag.md) and [the exterior lies in the first cut](exterior-first-cut.md).

**Remark (not formalized).** In the proof of the main theorem, $T$ is the [control space](../local-data/control/control-space.md) with the [orbit metric](../local-data/control/control-metric.md), which is a [compact metric space](../local-data/control/control-metric-properties.md), with the [cyclic action](../local-data/control/control-action.md), which is [free](../local-data/control/control-action-free.md) and [isometric](../local-data/control/control-action-isometric.md); $R$ is the buffer radius of the [fixed local data](../local-data/control/fixed-local-data.md); and $G_i=\mathbb Z/p^{\max(i,1)}$ with $\chi_i$ reduction modulo $p$, so $a_i=\max(i,1)\ge1$ and every $\chi_i$ is onto, level $0$ included; for $i\ge1$ this is $\mathbb Z/p^i$.

## Sources

- HS paper, Sections 2, 8 and 12.
- New: $T$ is an arbitrary nonempty compact free isometric $C_p$-space rather than the detector sphere, and the cut sets are faces of a cube rather than a ball and hemisphere flag.

## Depends on

## Proof depends on

- [Group sequence](../categories/asymptotic/group-sequence.md)
