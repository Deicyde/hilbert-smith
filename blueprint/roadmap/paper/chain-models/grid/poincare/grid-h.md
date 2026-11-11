---
article_id: af_888e8f865f768ac8a14844e6
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.gridH
---

# The grid homotopy

On the [grid complex](../cubical/cubical-torus-grid.md) $C(k)$ with $n$ factors, the map $H^{(n)}$ of degree $+1$ is defined by $H^{(0)}=0$ and $H^{(n+1)}=H^{(n)}\otimes A+1\otimes K$, [tensors of graded maps](../tensor/based-tensor-hom.md) of $H^{(n)}$ with the [degree-zero map A](circle-a.md) and of the [identity of degree zero](../tensor/id-deg0.md) with the [circle homotopy](circle-data/circle-k.md) $K$. Explicitly $H^{(n)}=\sum_{j=1}^n1^{\otimes(j-1)}\otimes K\otimes A^{\otimes(n-j)}$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [The circle complex vanishes in negative degrees](../cubical/circle-dim-neg.md)
- [Cubical torus grid](../cubical/cubical-torus-grid.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)
- [The degree-zero map A of the circle](circle-a.md)
- [The circle homotopy](circle-data/circle-k.md)
