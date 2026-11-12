---
article_id: af_cef2c99b33a69c4152008802
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.unitaryIsoIter
---

# Bounded extension of a unitary isomorphism

Let $\eta:F\cong G$ be a [unitary natural isomorphism](../../base/categories/unitary-isomorphism.md) of duality functors $(F,\xi),(G,\zeta):\mathcal A\to\mathcal B$. For $j\ge0$ put $C_{\mathbb Z^0}\eta=\eta$, and let $C_{\mathbb Z^{j+1}}\eta$ have at the object $M=(M_n)_n$ of $C_{\mathbb Z^{j+1}}\mathcal A$ the diagonal matrix with entries $(C_{\mathbb Z^j}\eta)_{M_n}$, of propagation $0$. Then $C_{\mathbb Z^j}\eta:C_{\mathbb Z^j}F\cong C_{\mathbb Z^j}G$ is a unitary natural isomorphism of the [bounded extensions](../../bounded/categories/bounded-functor.md).

*Proof sketch.* (Proof obligations, by induction on $j$.) Naturality holds entrywise: for a morphism $f=(f_{mn})$ of $C_{\mathbb Z^{j+1}}\mathcal A$, $(C_{\mathbb Z^{j+1}}G)(f)_{mn}\circ(C_{\mathbb Z^j}\eta)_{M_n}=(C_{\mathbb Z^j}G)(f_{mn})\,(C_{\mathbb Z^j}\eta)_{M_n}=(C_{\mathbb Z^j}\eta)_{N_m}\,(C_{\mathbb Z^j}F)(f_{mn})$ by naturality of $C_{\mathbb Z^j}\eta$. The inverse is the diagonal of the inverses. Unitarity holds entrywise, because the dual of a diagonal matrix is the diagonal of the duals and the duality data of $C_{\mathbb Z^{j+1}}F$ and $C_{\mathbb Z^{j+1}}G$ are those of $C_{\mathbb Z^j}F$ and $C_{\mathbb Z^j}G$ entrywise ([Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)).

## Sources

- New: levelwise.

## Depends on

- [Diagonal morphisms of $C_\mathbb Z(A)$](../../bounded/categories/bounded-diag.md)
- [Iterated bounded extension](../../bounded/categories/bounded-functor-iter.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
