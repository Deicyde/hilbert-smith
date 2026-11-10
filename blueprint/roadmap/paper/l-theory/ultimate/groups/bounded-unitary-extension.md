---
article_id: af_cef2c99b33a69c4152008802
declaration: def
origin: background
---

# Bounded extension of a unitary isomorphism

Let $\eta:F\cong G$ be a [unitary natural isomorphism](../../base/categories/unitary-isomorphism.md) of duality functors $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$. For $j\ge0$ put $C_{\mathbb Z^0}\eta=\eta$, and let $C_{\mathbb Z^{j+1}}\eta$ have at the object $M=(M_n)_n$ of $C_{\mathbb Z^{j+1}}\mathcal A$ the diagonal matrix with entries $(C_{\mathbb Z^j}\eta)_{M_n}$, of propagation $0$. Then $C_{\mathbb Z^j}\eta:C_{\mathbb Z^j}F\cong C_{\mathbb Z^j}G$ is a unitary natural isomorphism of the [bounded extensions](../../bounded/categories/bounded-functor.md).

*Proof sketch.* (Proof obligations, by induction on $j$.) Naturality holds entrywise: for $f=(f_{mn})$, $(C_\mathbb ZG)(f)_{mn}\circ\eta_{M_n}=G(f_{mn})\eta_{M_n}=\eta_{N_m}F(f_{mn})$. The inverse is the diagonal of the inverses. Unitarity holds entrywise, because the dual of a diagonal matrix is the diagonal of the duals and the duality data of $C_\mathbb ZF$ and $C_\mathbb ZG$ are $\xi$ and $\zeta$ entrywise.

## Sources

- New: levelwise.

## Depends on

- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
