---
article_id: af_f828bfdd9807276fdcb0ae3c
declaration: def
origin: background
---

# Bounded extension of a sum of functors

Let $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$ be duality functors and $F\oplus G$ their [sum](../../base/groups/sum-of-functors.md). For $j\ge0$ there is a unitary natural isomorphism
$$\sigma_j:C_{\mathbb Z^j}(F\oplus G)\cong C_{\mathbb Z^j}F\oplus C_{\mathbb Z^j}G$$
of duality functors $C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal B$: $\sigma_0$ is the identity, and $\sigma_{j+1}$ has at $M=(M_n)_n$ the diagonal matrix of propagation $0$ whose entry in position $n$ is $(\sigma_j)_{M_n}$ followed by the canonical isomorphism of the degreewise biproduct of [The bounded category](../../bounded/categories/bounded-category.md).

*Proof sketch.* (Proof obligations, by induction on $j$.) Both functors apply $F$ and $G$ entrywise, so $\sigma_{j+1}$ is natural entrywise, and its inverse is the diagonal of the inverses. The duality data of $C_\mathbb Z(F\oplus G)$ are $\xi\oplus\zeta$ followed by the canonical isomorphism of duals of sums, entrywise, which is also the duality data of $C_\mathbb ZF\oplus C_\mathbb ZG$ after the canonical isomorphism; so $\sigma_{j+1}$ is unitary.

## Sources

- New: levelwise.

## Depends on

- [Sums of functors](../../base/groups/sum-of-functors.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [The bounded category](../../bounded/categories/bounded-category.md)
