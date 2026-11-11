---
article_id: af_e95e508d3d22e22ae0953ba1
declaration: lemma
origin: background
statement: formalized
lean: HSP.ultL.of_trans
proof: formalized
---

# Stages are compatible with the transition

$\iota_{j+1}\circ t=\iota_j$ on $L^{\langle -j\rangle}_k(\mathcal A)$. Hence $\iota_{j+m}\circ t^m=\iota_j$ for every $m\ge0$. Here $t^m:L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-m\rangle}_k(\mathcal A)$ is the $m$-fold composite of transition maps, with $t^0=1$.

*Proof sketch.* This is the defining property of the maps into a colimit.

## Sources

- New: property of the colimit.

## Depends on

- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Ultimate L-group](ultimate-l-group.md)
