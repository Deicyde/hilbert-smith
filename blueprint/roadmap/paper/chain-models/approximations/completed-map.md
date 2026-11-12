---
article_id: af_1885db5a47125c28b80d3db7
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.completedMap
---
# Completed map

Fix a [local datum](../../local-data/chart/local-datum.md) and $a\in\mathbb Z_p$, and let $\widehat a$ be the [completed map on Euclidean space](maps/completed-map-euclid.md), $\widehat a(x)=x+\theta(x)(a\cdot x-x)$ for $|x|<2$ and $\widehat a(x)=x$ otherwise. Since $\widehat a$ is the identity off $B(0,3/2)$, it induces a self-map of the [torus](../grid/torus.md) $\mathbb T^n$ through the quotient $q:[-2,2]^n\to \mathbb T^n$, namely $x\mapsto q(\widehat a(\tilde x))$ with $\tilde x\in[-2,2)^n$ the lift of $x$, also written $\widehat a$.

## Sources
- HS paper, Section 9 (completed maps).
## Depends on
- [The lift](../torus/lift.md)
- [The quotient map](../torus/proj.md)
- [Local datum](../../local-data/chart/local-datum.md)
- [The completed map on Euclidean space](maps/completed-map-euclid.md)
- [The torus](../grid/torus.md)
