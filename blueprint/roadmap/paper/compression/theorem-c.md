---
declaration: theorem
origin: bridged
---
# Theorem C

Fix fixed local data, and let $G_i=\mathbb Z/p^i$ with $\chi_i$ reduction mod $p$. Let $\mathbf k$ be the mesh sequence. The compressed complex satisfies:
1. $C_i=0$ for $i<i_0$;
2. $(C,\hat\varphi)$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$;
3. $(\hat A,\hat B,\hat V,\delta)$ is a graph-type homotopy action of $\mathbf G$ on it;
4. $f$ is admissible, and $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{\mathbf k}(f_T)$.

*Proof sketch.* (1) holds by definition. Then apply the [compressed Poincaré](compressed-poincare.md) lemma, the [compressed action](compressed-action.md), [admissibility](test-map-admissible.md) and the [scalar image](compressed-scalar-image.md).

## Sources
- HS paper, Section 10 (compressed realization).
## Depends on
- [Compressed complex](compressed-complex.md), [graph-type action](../corner/graph-type-action.md), [labelled model class](labelled-model-class.md)
## Proof depends on
- [Compressed Poincaré](compressed-poincare.md), [compressed action](compressed-action.md), [test map admissible](test-map-admissible.md), [scalar image](compressed-scalar-image.md)
