---
article_id: af_5e654f5ddb7995444a14b6a9
declaration: lemma
origin: bridged
---
# The torus test map is homotopic to the cubical pinch

For [fixed local data](../local-data/control/fixed-local-data.md) and every $s>0$, the [torus test map](../chain-models/approximations/torus-test-map.md) $f_T:\mathbb T^n\to S^n$ is homotopic to the [cubical pinch](cubical-pinch.md) $\kappa$ for $n$ and $s$.

*Proof sketch.* Write $\tilde x\in[-2,2)^n$ for the lift of $x\in\mathbb T^n$, and recall $b=1/2$ and $c_\kappa$ from the cubical pinch.
1. Put $G(v,x)=\sigma_\rho((1-v)F_0(\tilde x)+v\tilde x)$ for $\tilde x\in\Omega$, and $\infty$ otherwise. The argument stays within $D$ of $\tilde x$ ([averaged map displacement](../local-data/chart/averaged-map-displacement.md)), so $G=\infty$ unless $|\tilde x|<\rho+D<1/2$. Thus $G$ is continuous on $[0,1]\times\mathbb T^n$ ([averaged map continuous](../local-data/chart/averaged-map-continuous.md), [pinch continuous](../local-data/chart/pinch-continuous.md)) and joins $f_T$ to $\sigma_\rho\circ(\text{lift})$.
2. Put $c_v(\tilde x)=(1-v)(\rho-|\tilde x|_2)+v\,c_\kappa(\tilde x)$ and $G'(v,x)=\tilde x/c_v(\tilde x)$ where $c_v(\tilde x)>0$, $\infty$ elsewhere. Then $c_v(0)>0$. If $|\tilde x|_\infty\ge b$, then $|\tilde x|_2\ge b>\rho$ and $c_\kappa(\tilde x)\le0$, so $c_v(\tilde x)\le0$. Hence $G'$ is continuous on $[0,1]\times\mathbb T^n$, by the gluing of [pinch homotopy](../local-data/chart/pinch-homotopy.md). It joins $\sigma_\rho\circ(\text{lift})$ to $\kappa$.

## Sources
- HS paper, Section 12. New: explicit homotopy; no degree classification.
## Depends on
- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Cubical pinch](cubical-pinch.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
## Proof depends on
- [Test map](../local-data/chart/test-map.md)
- [Averaged map continuous](../local-data/chart/averaged-map-continuous.md)
- [Averaged map displacement](../local-data/chart/averaged-map-displacement.md)
- [Pinch continuous](../local-data/chart/pinch-continuous.md)
- [Pinch homotopy](../local-data/chart/pinch-homotopy.md)
