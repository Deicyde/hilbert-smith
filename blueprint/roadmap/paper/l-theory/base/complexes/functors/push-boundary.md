---
article_id: af_c3b1a5ea46f6571a0dd36c84
declaration: lemma
origin: background
statement: formalized
lean: HSP.StructureCx.d_push_apply
proof: formalized
---

# Pushforward commutes with the boundary

For a chain map $g:C\to D$ and $x\in M(C)_n$, the [pushforward](../structure-push.md) satisfies $\partial(g_\%x)=g_\%(\partial x)$ in $M(D)_m$, for the boundary of the [structure complex](../structure-complex.md).

*Proof sketch.* $g_\%$ is a chain map $M(C)\to M(D)$; this is the commuting square evaluated at $x$.

## Sources

- New: direct from the definitions.

## Depends on

- [Pushforward of structures](../structure-push.md)
- [Structure complex](../structure-complex.md)
