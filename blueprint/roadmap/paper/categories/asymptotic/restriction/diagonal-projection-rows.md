---
article_id: af_dc4e0fc960f089a4f89adb76
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.mkHom_comp_trunc_eq
---

# Factorization through a diagonal projection, rows

Let $u:N\to M$ be a sequence of $G_i$-equivariant matrices with propagation tending to $0$ such that, eventually, every nonzero entry of $u_i$ lies in a row $(g,k)$ with $P(i,k)$. Then $[p_P][u]=[u]$ in the [asymptotic category](../asymptotic-category.md), for the [diagonal coordinate projection](diagonal-projection.md) $p_P$ of $M$.

*Proof sketch.* Multiplying by $p_P$ on the left kills exactly the rows outside $P$, which eventually vanish; morphisms are taken modulo eventual equality.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Diagonal coordinate projection](diagonal-projection.md)
- [Asymptotic category](../asymptotic-category.md)

## Proof depends on

- [Equality of classes](../structure/class-eq.md)
