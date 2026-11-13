---
article_id: af_4e0756a1db5dde6f9e596dda
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Compression.bound_tendsto
---
# The bound sequence is null

The [bound sequence](bound-sequence.md) $(\delta_i)$ is a null sequence: $\delta_i\to0$.

*Proof.* $\delta_i=\epsilon'_i$ for all $i\ge i_0$, and $(\epsilon'_i)$ is a null sequence by [buffers hold eventually](buffer-eventually.md).

## Sources
- New: one bound for every estimate of the compression.

## Depends on

- [Bound sequence](bound-sequence.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)

## Proof depends on

- [Buffers hold eventually](buffer-eventually.md)
- [Start index](start-index.md)
- [Buffer conditions](buffer-conditions.md)
