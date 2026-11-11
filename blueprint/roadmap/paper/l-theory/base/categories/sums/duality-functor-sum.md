---
article_id: af_393def6191a16073090c1418
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.biprod
---

# Sum of duality functors

Let $(F,\xi),(G,\zeta):\mathcal B\to\mathcal B'$ be [duality functors](../duality-functor.md). The *sum* $F\oplus G$ is the functor $M\mapsto FM\oplus GM$, $f\mapsto Ff\oplus Gf$. Its duality isomorphism at $M$ is $\xi_M\oplus\zeta_M:F(M^*)\oplus G(M^*)\to FM^*\oplus GM^*$ followed by the inverse of the [canonical isomorphism](dual-biproduct.md) $(FM\oplus GM)^*\cong FM^*\oplus GM^*$. With these data $F\oplus G$ is a duality functor.

*Proof sketch.* $F\oplus G$ is $\mathbb Q$-linear because $F$ and $G$ are and $\oplus$ is linear in each summand. Naturality and the condition on the dual of the duality isomorphism are checked on each summand. On the $F$ summand they reduce to the same conditions for $\xi$, because the canonical isomorphism followed by $\iota_{FM}^*$ is the projection onto $FM^*$; the $G$ summand is the same with $\zeta$.

## Sources

- New: the sum construction of [Sums of functors](../../groups/sum-of-functors.md), as a duality functor.

## Depends on

- [Duality functor](../duality-functor.md)
- [Dual of a binary sum](dual-biproduct.md)
- [A duality category has binary direct sums](../dual-binary-biproducts.md)
