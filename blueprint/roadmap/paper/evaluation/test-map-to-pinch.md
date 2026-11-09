---
declaration: lemma
origin: bridged
---
# The torus test map is homotopic to the cubical pinch

The [torus test map](../chain-models/torus-test-map.md) $f_T$ is homotopic to $\kappa$ through continuous maps $T^n\to S^n$.

*Proof sketch.*
1. Put $G(v,x)=\sigma_\rho((1-v)F_0(\tilde x)+v\tilde x)$ for $\tilde x\in\Omega$, and $\infty$ otherwise. The argument stays within $D$ of $\tilde x$, so $G=\infty$ unless $|\tilde x|<\rho+D<1/2$. Thus $G$ is continuous on $T^n$ and joins $f_T$ to $\sigma_\rho\circ(\text{lift})$.
2. Put $c_v=(1-v)(\rho-|\tilde x|_2)+v\,c_\kappa(\tilde x)$ and $G'(v,x)=\tilde x/c_v$ where $c_v>0$, $\infty$ elsewhere. Then $c_v(0)>0$. If $|\tilde x|_\infty\ge b$, then $|\tilde x|_2\ge b>\rho$, so $c_v\le0$. Hence $G'$ is continuous on $T^n$, by the gluing of [pinch homotopy](../local-data/chart/pinch-homotopy.md). It joins $\sigma_\rho\circ(\text{lift})$ to $\kappa$.

## Sources
- HS paper, Section 12. New: explicit homotopy; no degree classification.
## Depends on
- [Cubical pinch](cubical-pinch.md), [torus test map](../chain-models/torus-test-map.md)
## Proof depends on
- [Test map](../local-data/chart/test-map.md), [averaged map continuous](../local-data/chart/averaged-map-continuous.md), [averaged map displacement](../local-data/chart/averaged-map-displacement.md), [pinch continuous](../local-data/chart/pinch-continuous.md), [pinch homotopy](../local-data/chart/pinch-homotopy.md)
