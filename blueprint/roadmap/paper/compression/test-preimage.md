---
article_id: af_79e6ed62d54c7bdf468a4030
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.testPreimage
---
# The preimage of the buffer ball

Take [fixed local data](../local-data/control/fixed-local-data.md), with pinch radius $\rho$ and buffer radius $t$, and let $f_T:\mathbb T^n\to S^n$ be the [torus test map](../chain-models/approximations/torus-test-map.md) of radius $\rho$. Then $K_t=f_T^{-1}(\overline B(0,t))\subseteq\mathbb T^n$, where the closed Euclidean ball $\overline B(0,t)\subseteq\mathbb R^n$ is viewed in $S^n=\mathbb R^n\cup\{\infty\}$.

## Sources
- HS paper, Section 10 (far simplices).

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [The torus](../chain-models/grid/torus.md)

## Proof depends on

- [Torus test map](../chain-models/approximations/torus-test-map.md)
