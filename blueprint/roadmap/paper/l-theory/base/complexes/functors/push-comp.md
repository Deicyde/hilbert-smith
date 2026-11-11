---
article_id: af_d1b82b5f84e6866c87f78bc2
declaration: lemma
origin: background
statement: formalized
lean: HSP.StructureCx.push_comp
proof: formalized
---

# Pushforward preserves composition

For chain maps $g:C\to D$ and $h:D\to E$, the [pushforwards](../structure-push.md) satisfy $(hg)_\%=h_\%g_\%$ as chain maps $M(C)\to M(E)$.

*Proof sketch.* On the component $(p,q)$ of $f\in M(C)_n$, both sides are $h_pg_pf_{p,q}g_q^*h_q^*$, since $(h_qg_q)^*=g_q^*h_q^*$.

## Sources

- New: direct from the definitions.

## Depends on

- [Pushforward of structures](../structure-push.md)
- [Structure complex](../structure-complex.md)
