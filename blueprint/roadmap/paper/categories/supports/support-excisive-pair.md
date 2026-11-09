---
article_id: af_da983e66a6851c8ee5ac0770
declaration: def
origin: bridged
---

# Support excisive pair

Let $A,B\subset X$ be closed and invariant, and put $S=A\cup B$. Then the $A$- and $B$-supported objects form an [excisive pair](../../l-theory/ultimate/boundary/excisive-pair.md) $(\mathcal A_A,\mathcal A_B)$ in $\mathcal A_S$, with $e$ the [excision equivalence](excision.md).

*Proof sketch.* [Support filtration](support-filtration.md) for $A\subset S$ and for $B\subset S$ gives the two filtrations. By [support intersection](support-intersection.md), the predicate $\mathcal A_A\cap\mathcal A_B$ equals $\mathcal A_{A\cap B}$. So the intersection filtration is the support filtration for $A\cap B\subset A$, transported along this equality, and the induced functor is the excision equivalence.

## Sources

- HS paper, Section 2

## Depends on

- [Excisive pair of filtrations](../../l-theory/ultimate/boundary/excisive-pair.md)
- [Excision equivalence](excision.md)

## Proof depends on

- [Support filtration](support-filtration.md)
- [Support intersection](support-intersection.md)
