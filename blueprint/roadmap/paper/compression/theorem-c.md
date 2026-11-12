---
article_id: af_237b8625032bf38c38d89a65
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.Compression.theoremC
---
# Theorem C

Take [fixed local data](../local-data/control/fixed-local-data.md), with buffer radius $R$, [torus test map](../chain-models/approximations/torus-test-map.md) $f_T$ and [control space](../local-data/control/control-space.md) $T$ (possibly empty), with the [orbit metric](../local-data/control/control-metric.md) and the [cyclic action](../local-data/control/control-action.md). Let $Z_0\subseteq S^n$ be the [exterior](../corner/exterior.md) for $n$ and $R$, and $Z=T\times Z_0$. For $i\in\mathbb N$ let $G_i=\mathbb Z/p^{\max(i,1)}$ and $\chi_i$ reduction mod $p$; for $i\ge1$ this is $\mathbb Z/p^i$, and level $0$ carries nothing because $C$ and every compressed map vanish below the start index $i_0\ge1$. Let $(C,\hat\varphi)$ be the [compressed complex](compressed-complex.md) with its [compressed maps](compressed-maps.md) and the [bound sequence](bound-sequence.md) $(\delta_i)$. Then:
1. $(C,\hat\varphi)$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, whose chain objects are objects of $\mathcal B_{\mathbf 1,Z}(T\times S^n)$;
2. if $T$ is nonempty, then for every $s$ with $0<s<R/\sqrt n$ these data form [standing data](../corner/standing-data.md) (the [standing data of the compression](compressed-standing-data.md)), and $(\hat A,\hat B,\hat V,(\delta_i))$ is a [graph-type homotopy action](../corner/actions/graph-type-action.md) of $\mathbf G=(G_i,\chi_i)$ on $(C,\hat\varphi)$;
3. $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}$ in $\mathbb L_N(\mathcal B_{\mathbf 1,Z_0}(S^n))$, where $\operatorname{cls}$ is applied to $(C,\hat\varphi)$ read in the idempotent completion through the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md), $U'$ is [forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md) for $T$, $R$ and the trivial group sequence, and $\mathfrak m_{f_T}$ is the [germ](../evaluation/germ.md) of the labelling $c=f_T$.

Clauses (1) and (3) are well formed for every $T$: $T$ is a compact metric space ([the orbit metric metrizes the control space](../local-data/control/control-metric-properties.md), [the control space is compact](../local-data/control/control-space-compact.md)) with an [isometric](../local-data/control/control-action-isometric.md) $C_p$-action, so $Z$ is closed and invariant ([the exterior is closed](../corner/exterior-closed.md)) and $\mathcal B_{\mathbf 1,Z}(T\times S^n)$ and $U'$ are defined.

This theorem rests on no open statement.

*Proof sketch.* (1) is [the compressed complex is Poincaré](compressed-poincare.md), (2) is [the compressed action](compressed-action.md), and (3) is the [scalar image](compressed-scalar-image.md).

**Remark (not formalized).** If $T$ is empty, then $Z^+$ is empty, there are no retained cells, $C$ is the zero object, and (3) says $\mathfrak m_{f_T}=0$. The final proof does not use this remark: in the empty case it shows $\operatorname{cls}(C,\hat\varphi)=0$ itself, because $T\times S^n$ is empty, and then reads $\mathfrak m_{f_T}=0$ off (3).

## Sources
- HS paper, Section 10 (compressed realization).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
- [Control space](../local-data/control/control-space.md)
- [Orbit metric](../local-data/control/control-metric.md)
- [Cyclic action](../local-data/control/control-action.md)
- [The orbit metric metrizes the control space](../local-data/control/control-metric-properties.md)
- [The control space is compact](../local-data/control/control-space-compact.md)
- [The cyclic action is isometric](../local-data/control/control-action-isometric.md)
- [Exterior](../corner/exterior.md)
- [The exterior is closed](../corner/exterior-closed.md)
- [Standing data](../corner/standing-data.md)
- [Compressed complex](compressed-complex.md)
- [Compressed maps](compressed-maps.md)
- [Start index](start-index.md)
- [Bound sequence](bound-sequence.md)
- [Standing data of the compression](compressed-standing-data.md)
- [Strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Graph-type action](../corner/actions/graph-type-action.md)
- [Forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md)
- [Germ](../evaluation/germ.md)
- [Ultimate L-group and cls](../l-theory/ultimate/groups/ultimate-l-group.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [L-group](../l-theory/base/groups/l-group.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)

## Proof depends on

- [Compressed Poincaré](compressed-poincare.md)
- [Compressed action](compressed-action.md)
- [Scalar image](compressed-scalar-image.md)
