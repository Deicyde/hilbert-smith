---
article_id: af_fbd51612a4894414fd6d2922
declaration: lemma
origin: background
statement: formalized
lean: HSP.StructureCx.push_id
proof: formalized
---

# Pushforward preserves identities

For a complex $C$, the [pushforward](../structure-push.md) along the identity is the identity: $(1_C)_\%=1_{M(C)}$.

*Proof sketch.* On each component, $1\circ f_{p,q}\circ1^*=f_{p,q}$.

## Sources

- New: direct from the definitions.

## Depends on

- [Pushforward of structures](../structure-push.md)
- [Structure complex](../structure-complex.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
