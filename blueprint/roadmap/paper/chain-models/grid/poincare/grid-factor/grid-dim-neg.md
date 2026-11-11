---
article_id: af_784aae0c6954ba83deba2271
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.gridComplex_dim_neg
---

# The grid complex vanishes in negative degrees

For every $k$ and $n$, the [grid complex](../../cubical/cubical-torus-grid.md) $C(k)$ with $n$ circle factors vanishes in negative degrees: $C(k)_q=0$ for $q<0$.

*Proof sketch.* For $n=0$ it is the unit complex, $\mathbb Q$ in degree $0$. For $n+1$ it is a tensor product with the circle complex, which vanishes in negative degrees ([the tensor product vanishes in negative degrees](../../tensor/tensor-dim-neg.md)).

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Cubical torus grid](../../cubical/cubical-torus-grid.md)

## Proof depends on

- [The tensor product vanishes in negative degrees](../../tensor/tensor-dim-neg.md)
