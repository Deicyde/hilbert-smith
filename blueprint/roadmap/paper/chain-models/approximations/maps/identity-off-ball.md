---
article_id: af_8b719b7dcd8171d5d39cf43c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.identity_off_ball
---

# Completed and track maps are the identity off B(0,3/2)

For $|x|\ge3/2$ and all $a,b,c\in\mathbb Z_p$, $t\in[0,1]$: $\widehat a(x)=x$ and $L_{a,b,c,t}(x)=x$, for the [completed map](completed-map-euclid.md) and the [track map](track-map-euclid.md) on $\mathbb R^n$.

*Proof.* For $|x|\ge3/2$ the [cutoff](completed-cutoff.md) vanishes, so $\widehat a(x)=x$. Then $L_{a,b,c,t}(x)=(1-t)x+tx=x$.

## Sources

- New: companion of the completed maps and their tracks.

## Depends on

- [The completed map on Euclidean space](completed-map-euclid.md)
- [The track map on Euclidean space](track-map-euclid.md)

## Proof depends on

- [Completed cutoff](completed-cutoff.md)
