---
article_id: af_82416bc0dcaa0408bf9f872f
declaration: lemma
origin: background
statement: formalized
lean: HSP.Bounded.map_isStrict
proof: formalized
---

# Bounded extensions of strict functors are strict

If a [duality functor](../base/categories/duality-functor.md) $(F,\xi):A\to A'$ is strict, then so is its [bounded extension](categories/bounded-functor.md) $C_\mathbb Z(F,\xi):C_\mathbb Z(A)\to C_\mathbb Z(A')$.

*Proof sketch.* Strictness of $F$ gives $F(M_n^*)=(FM_n)^*$ with $\xi_{M_n}$ the identity, for every $n$. Hence $C_\mathbb ZF(M^*)=(C_\mathbb ZF\,M)^*$ entrywise, and $(C_\mathbb Z\xi)_M$, the diagonal matrix $(\xi_{M_n})_n$, is the identity.

## Sources

- New: entrywise.

## Depends on

- [Bounded extension of a duality functor](categories/bounded-functor.md)
- [Duality functor](../base/categories/duality-functor.md)
