---
declaration: lemma
origin: bridged
---

# Classes over $\mathcal V$ lift

Every $x\in\mathbb L_4(\mathcal V)$ is $q_*y$ for some $y\in\mathbb L_4(\mathcal P)$.

*Proof sketch.* $i_*\partial x=0$ in $\mathbb L_3(\mathcal P)$ by [D4](../l-theory/D4.md). Since $\pi_i\circ i$ is the coordinate functor of $\mathcal S$, injectivity in [E6](../l-theory/E6.md) and functoriality [D2](../l-theory/D2.md) give $\partial x=0$. Exactness at the quotient [D5](../l-theory/D5.md) then provides $y$.

## Sources

- HS paper, Section 3

## Depends on

- [Sequence categories](sequence-categories.md)
- [Ultimate L-theory](../l-theory/D1.md)

## Proof depends on

- [Finite-support filtration](finite-support-filtration.md)
- [D4](../l-theory/D4.md), [D5](../l-theory/D5.md), [E6](../l-theory/E6.md)
