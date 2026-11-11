---
article_id: af_e23bdfa64e3bb3bc5b64452e
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.map
---

# Bounded extension of a duality functor

Let $(F,\xi):A\to A'$ be a [duality functor](../../base/categories/duality-functor.md) between additive duality categories. Its *bounded extension* is the duality functor
$$C_\mathbb Z(F,\xi)=(C_\mathbb Z F,\,C_\mathbb Z\xi):C_\mathbb Z(A)\to C_\mathbb Z(A'),$$
where $C_\mathbb Z F$ is the [entrywise functor](entrywise-functor.md), $(M_n)\mapsto(FM_n)$ and $(f_{mn})\mapsto(Ff_{mn})$, and the duality isomorphism $(C_\mathbb Z\xi)_M:C_\mathbb ZF(M^*)\to(C_\mathbb ZF\,M)^*$ is the diagonal matrix $(\xi_{M_n})_n$, of propagation $0$. Here $C_\mathbb Z(A)$ and $C_\mathbb Z(A')$ carry [the induced duality](bounded-duality.md).

*Proof sketch.* (1) $C_\mathbb ZF$ is a $\mathbb Q$-linear functor ([The entrywise functor](entrywise-functor.md)). (2) $C_\mathbb Z\xi$ is natural because each $\xi$ is, entry by entry. (3) $((C_\mathbb Z\xi)_M)^*$ is the diagonal matrix $(\xi_{M_n}^*)_n=(\xi_{M_n^*})_n=(C_\mathbb Z\xi)_{M^*}$.

## Sources

- New: apply $F$ entrywise.

## Depends on

- [Diagonal morphisms of $C_\mathbb Z(A)$](bounded-diag.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [The induced duality](bounded-duality.md)
- [Iterated bounded categories](iterated-bounded-category.md)
- [The entrywise functor](entrywise-functor.md)
