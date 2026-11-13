---
article_id: af_d8f82bb13d9772eb8be17ae9
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.ChainModels.Torus.dist₂_proj_le
---

# The quotient map does not increase distances

For $y,y'\in\mathbb R^n$, $d_2(q(y),q(y'))\le|y-y'|$.

*Proof sketch.* Each circle distance $d(y_j,y'_j)$ is at most $|y_j-y'_j|$.

## Sources

- New: the torus closing of the chart cube $[-2,2]^n$.

## Depends on

- [The quotient map](proj.md)
- [The quotient Euclidean metric](dist2.md)

## Proof depends on

- [The torus](../grid/torus.md)
