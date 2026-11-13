---
article_id: af_24f4bae65d1d72a7e0fe9c11
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.sphereProp
---

# Sphere propagation

Fix a local datum and a radius $\rho$, with [torus test map](../../approximations/torus-test-map.md) $f_T$. The *sphere propagation* of a matrix $u$ whose source and target cells carry torus labels $x_b$ and $x'_{b'}$ is its [propagation](../../../categories/asymptotic/propagation.md) for the sphere labels $f_T(x_b)$, $f_T(x'_{b'})$ in the [round sphere](../../../corner/round-sphere.md) $S^n$ with its metric $d_S$.

## Sources

- HS paper, Sections 9-10 (propagation in sphere labels).

## Depends on

- [The torus](../torus.md)
- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [Propagation](../../../categories/asymptotic/propagation.md)
- [Torus test map](../../approximations/torus-test-map.md)
- [Round sphere](../../../corner/round-sphere.md)
