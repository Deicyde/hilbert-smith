---
article_id: af_9a10524d4ca527e39adfc191
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.startIndex
---
# Start index

Fix the null sequence $(\epsilon'_i)$ chosen in [buffers hold eventually](buffer-eventually.md). The *start index* $i_0$ is the least integer $i_0\ge1$ such that the [buffer conditions](buffer-conditions.md) hold with $(\epsilon'_i)$ for every $i\ge i_0$.

## Sources
- New: the index from which the compression is defined.

## Depends on

- [Buffer conditions](buffer-conditions.md)
- [Buffers hold eventually](buffer-eventually.md)
