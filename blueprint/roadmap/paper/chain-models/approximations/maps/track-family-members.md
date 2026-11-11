---
article_id: af_37f7e542237f49abe1146e7e
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.trackFamily_mem
---

# The track family contains the completed maps and the identity

The [track family](track-family.md) $\mathcal F$ contains every [completed map](../completed-map.md) $\widehat a=L_{a,0,a,t}$ of the torus, and the identity $L_{0,0,0,t}$.

*Proof.* $\widehat0$ is the identity of $\mathbb R^n$, so $L_{a,0,a,t}=(1-t)\widehat a+t\widehat a=\widehat a$ and $L_{0,0,0,t}=\mathrm{id}$.

## Sources

- New: companion of the completed maps and their tracks.

## Depends on

- [The track family](track-family.md)
- [Completed map](../completed-map.md)

## Proof depends on

- [The completed map on Euclidean space](completed-map-euclid.md)
- [The track map on Euclidean space](track-map-euclid.md)
