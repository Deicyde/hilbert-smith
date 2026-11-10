---
article_id: af_237b8625032bf38c38d89a65
declaration: theorem
origin: bridged
---
# Theorem C

Take [fixed local data](../local-data/control/fixed-local-data.md), with buffer radius $R$, [torus test map](../chain-models/approximations/torus-test-map.md) $f_T$ and [control space](../local-data/control/control-space.md) $T$ (possibly empty). Let $Z_0$ and $Z=T\times Z_0$ be the exterior of the [standing data](../corner/standing-data.md) for $T$ and $R$. For levels $i\ge1$ let $G_i=\mathbb Z/p^i$ and $\chi_i$ reduction mod $p$. Let $(C,\hat\varphi)$ be the [compressed complex](compressed-complex.md) with its [compressed maps](compressed-maps.md) and the bound sequence $(\delta_i)$ of the [start index](start-index.md). Then:
1. $(C,\hat\varphi)$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, whose chain objects are objects of $\mathcal B_{\mathbf 1,Z}(T\times S^n)$;
2. if $T$ is nonempty, then for every $s$ with $0<s<R/\sqrt n$ these data form standing data, and $(\hat A,\hat B,\hat V,(\delta_i))$ is a [graph-type homotopy action](../corner/actions/graph-type-action.md) of $\mathbf G=(G_i,\chi_i)$ on $(C,\hat\varphi)$;
3. $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}$ in $\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n))$, where $U'$ is the functor of [scalar image of the corner](../corner/theorem/scalar-image.md) and $\mathfrak m_{f_T}$ is the [germ](../evaluation/germ.md) of the labelling $c=f_T$.

This theorem rests on no open statement; it takes from the scalar image of the corner only the definition of $U'$, the functor induced on exterior quotients by [forgetting the control space](../categories/functors/forget-control.md), and not the lemma there, which rests on idempotent splitting.

*Proof sketch.* (1) is [the compressed complex is Poincaré](compressed-poincare.md), (2) is [the compressed action](compressed-action.md), and (3) is the [scalar image](compressed-scalar-image.md).

**Remark (not formalized).** Nothing in the construction uses a point of $T$: labels are needed only on buffered cells, whose lifts lie in $Z^+$. If $T$ is empty, then $Z^+$ is empty, there are no retained cells, $C$ is the zero object, and (3) says $\mathfrak m_{f_T}=0$, as the final proof uses.

## Sources
- HS paper, Section 10 (compressed realization).
## Depends on
- [Fixed local data](../local-data/control/fixed-local-data.md), [torus test map](../chain-models/approximations/torus-test-map.md), [control space](../local-data/control/control-space.md), [standing data](../corner/standing-data.md), [compressed complex](compressed-complex.md), [compressed maps](compressed-maps.md), [start index](start-index.md), [strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md), [exterior quotient](../categories/supports/exterior-quotient.md), [graph-type action](../corner/actions/graph-type-action.md), [scalar image of the corner](../corner/theorem/scalar-image.md), [forgetting the control space](../categories/functors/forget-control.md), [induced functor on exterior quotients](../categories/supports/exterior-functor.md), [germ](../evaluation/germ.md), [ultimate L-group and cls](../l-theory/ultimate/groups/ultimate-l-group.md)
## Proof depends on
- [Compressed Poincaré](compressed-poincare.md), [compressed action](compressed-action.md), [scalar image](compressed-scalar-image.md)
