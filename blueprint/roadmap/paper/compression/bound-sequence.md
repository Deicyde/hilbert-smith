---
article_id: af_a4acfddceb060d06b61f6413
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.bound
---
# Bound sequence

Fix the null sequence $(\epsilon'_i)$ chosen in [buffers hold eventually](buffer-eventually.md), and let $i_0$ be the [start index](start-index.md). The *bound sequence* is $\delta_i=\epsilon'_i$ for $i\ge i_0$ and $\delta_i=0$ for $i<i_0$.

## Sources
- New: one bound for every estimate of the compression.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [Buffer conditions](buffer-conditions.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Start index](start-index.md)
