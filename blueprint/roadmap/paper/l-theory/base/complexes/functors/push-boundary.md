---
article_id: af_c3b1a5ea46f6571a0dd36c84
declaration: lemma
origin: background
statement: formalized
lean: HSP.StructureCx.d_push_apply
proof: formalized
---

# Pushforward commutes with the boundary

Let $g:C\to D$ be a chain map of $\mathbb Z$-graded complexes in a duality category, not necessarily bounded. For all integers $n,m$ and $x\in M(C)_n$, the [pushforward](../structure-push.md) satisfies $\partial(g_\%x)=g_\%(\partial x)$ in $M(D)_m$. Here $\partial:M(-)_n\to M(-)_m$ is the component of the boundary of the [structure complex](../structure-complex.md), which is zero unless $m=n-1$.

*Proof sketch.* $g_\%$ is a chain map $M(C)\to M(D)$; this is the commuting square evaluated at $x$.

## Sources

- New: direct from the definitions.

## Depends on

- [Pushforward of structures](../structure-push.md)
- [Structure complex](../structure-complex.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
