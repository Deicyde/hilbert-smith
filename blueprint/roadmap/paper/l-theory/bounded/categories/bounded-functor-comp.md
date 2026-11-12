---
article_id: af_2fc95d9c321cb0a287f03476
declaration: theorem
origin: background
statement: formalized
lean: HSP.Bounded.mapIter_id_comp
proof: formalized
---

# Bounded extension is functorial

Let $(F,\xi):A\to A'$ and $(G,\zeta):A'\to A''$ be duality functors and $j\ge0$. Then $C_{\mathbb Z^j}(\mathrm{id}_A)=\mathrm{id}_{C_{\mathbb Z^j}(A)}$ and $C_{\mathbb Z^j}\big((G,\zeta)\circ(F,\xi)\big)=C_{\mathbb Z^j}(G,\zeta)\circ C_{\mathbb Z^j}(F,\xi)$ as duality functors, duality data included, where $C_{\mathbb Z^j}$ is the [iterated bounded extension](bounded-functor-iter.md) and composites carry the duality data of [Duality functor](../../base/categories/duality-functor.md).

*Proof sketch.* (1) The case $j=1$, for any duality functors. Both sides of each equation agree on objects and on morphisms, entry by entry. The duality data agree: $C_\mathbb Z(\mathrm{id})$ has the identity diagonal, and for the composite, at $M$, the left side is the diagonal matrix $(\zeta_{FM_n}G(\xi_{M_n}))_n$ and the right side is $(\zeta_{FM_n})_n\circ C_\mathbb ZG\big((\xi_{M_n})_n\big)$, the same matrix. (2) Induction on $j$, the case $j=0$ being trivial: since $C_{\mathbb Z^{j+1}}=C_\mathbb ZC_{\mathbb Z^j}$ ([Iterated bounded categories](iterated-bounded-category.md)), $C_{\mathbb Z^{j+1}}(GF)=C_\mathbb Z(C_{\mathbb Z^j}G\circ C_{\mathbb Z^j}F)=C_{\mathbb Z^{j+1}}G\circ C_{\mathbb Z^{j+1}}F$ by (1) for $C_{\mathbb Z^j}F$ and $C_{\mathbb Z^j}G$, and likewise for the identity.

## Sources

- New: entrywise.

## Depends on

- [Bounded extension of a duality functor](bounded-functor.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Iterated bounded extension](bounded-functor-iter.md)
- [Identity and composite duality functors](../../base/categories/duality-functors/composite-duality-functor.md)

## Proof depends on

- [Iterated bounded categories](iterated-bounded-category.md)
