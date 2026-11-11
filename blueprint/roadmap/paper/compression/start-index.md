---
article_id: af_9a10524d4ca527e39adfc191
declaration: def
origin: bridged
---
# Start index and bound sequence

Fix the null sequence $(\epsilon'_i)$ chosen in [buffers hold eventually](buffer-eventually.md). The *start index* $i_0\ge1$ is the least index such that items (1)-(3) of that lemma hold with $(\epsilon'_i)$ for every $i\ge i_0$. The *bound sequence* is $\delta_i=\epsilon'_i$ for $i\ge i_0$ and $\delta_i=0$ for $i<i_0$; it is a null sequence.

## Sources
- New: the index from which the compression is defined, and one bound for every estimate.

## Depends on

- [Buffers hold eventually](buffer-eventually.md)
