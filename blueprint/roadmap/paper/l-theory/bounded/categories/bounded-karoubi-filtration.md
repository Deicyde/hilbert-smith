---
article_id: af_15dfabb847e433932a756aef
declaration: def
origin: cited
statement: formalized
lean: HSP.Bounded.karoubiFiltration
---

# Bounded Karoubi filtrations

Let $U\subset A$ be an involution-invariant Karoubi filtration, and let $C_\mathbb Z(U)\subset C_\mathbb Z(A)$ be the [bounded subcategory](bounded-sub.md), of the objects $M$ with every $M_n$ in $U$. For an object $M$ of $C_\mathbb Z(A)$ let $\mathcal D(M)$ be the set of diagonal idempotents $p=(p_n)$, of propagation $0$, with $p_n\in\mathcal D(M_n)$ for every $n$. With these sets, $C_\mathbb Z(U)\subset C_\mathbb Z(A)$ is an involution-invariant Karoubi filtration.

*Proof sketch.*
1. $C_\mathbb Z(U)$ is full, additive and closed under the duality ([the bounded subcategory is closed under sums and duals](bounded-sub-additive.md)).
2. Each $p\in\mathcal D(M)$ is a $C_\mathbb Z(U)$-decomposition: the degreewise splittings of $p_n$ through $E_n\in U$ and of $1-p_n$ assemble into splittings of propagation $0$. $\mathcal D(M)$ is nonempty and directed degreewise.
3. Factorization. Let $g:V\to M$ have propagation $r$, with $V\in C_\mathbb Z(U)$. In degree $n$ each of the finitely many components $g_{nm}$, $|m-n|\le r$, has source $V_m\in U$, so some decomposition in $\mathcal D(M_n)$ fixes it; since $\mathcal D(M_n)$ is directed, some $p_n\in\mathcal D(M_n)$ lies above all of them, and then $p_ng_{nm}=g_{nm}$ for all $m$. Then $p=(p_n)$ has $pg=g$. Maps $M\to V$ are handled in the same way.
4. Duality. $p^*=(p_n^*)$, and $p_n\in\mathcal D(M_n)$ iff $p_n^*\in\mathcal D(M_n^*)$.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [The induced duality](bounded-duality.md)
- [The bounded subcategory](bounded-sub.md)
- [The bounded subcategory is closed under sums and duals](bounded-sub-additive.md)
