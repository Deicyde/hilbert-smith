---
article_id: af_755cf376b83a7af3582ae940
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.completedMapEuclid
---

# The completed map on Euclidean space

Fix a [local datum](../../../local-data/chart/local-datum.md) and $a\in\mathbb Z_p$. The *completed map* on $\mathbb R^n$ is $\widehat a(x)=x+\theta(x)(a\cdot x-x)$ for $|x|<2$, and $\widehat a(x)=x$ otherwise, with $\theta$ the [completed cutoff](completed-cutoff.md) and $a\cdot x$ the action of the local datum, defined on $B(0,2)$.

## Sources

- New: companion of the completed maps and their tracks.

## Depends on

- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [Completed cutoff](completed-cutoff.md)
