---
article_id: af_1bc986af5ee74068e6685fff
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.standingData
---
# Standing data of the compression

Take [fixed local data](../local-data/control/fixed-local-data.md) with buffer radius $R$, suppose the [control space](../local-data/control/control-space.md) $T$ is nonempty, and let $0<s<R/\sqrt n$. The *standing data of the compression* is the [standing data](../corner/standing-data.md) consisting of the prime $p$; the group sequence $G_i=\mathbb Z/p^{\max(i,1)}$, $i\in\mathbb N$, with $\chi_i$ reduction mod $p$, which is onto because $p\mid p^{\max(i,1)}$; the control space $T$ with the [orbit metric](../local-data/control/control-metric.md) and the [cyclic action](../local-data/control/control-action.md), which is compact ([the control space is compact](../local-data/control/control-space-compact.md)), nonempty by hypothesis, and on which the action is [free](../local-data/control/control-action-free.md) and [isometric](../local-data/control/control-action-isometric.md); the dimension $n$, which is at least $1$ because the action moves the origin of $\mathbb R^n$; the buffer radius $R>0$; and $s$.

## Sources
- HS paper, Section 10.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [The control space](../local-data/control/control-space.md)
- [Standing data](../corner/standing-data.md)
- [The orbit metric on the control space](../local-data/control/control-metric.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The control space is compact](../local-data/control/control-space-compact.md)
- [The cyclic action is free](../local-data/control/control-action-free.md)
- [The cyclic action is isometric](../local-data/control/control-action-isometric.md)
