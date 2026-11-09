---
declaration: def
origin: bridged
---

# Relabelling isomorphism

Let $M=(n_i,x_i)$ and $M'=(n_i,x'_i)$ be objects with $\max_kd(x_i(k),x'_i(k))\to0$. The identity matrices give a [unitary isomorphism](../l-theory/base/unitary-isomorphism.md) $M\to M'$.

*Proof sketch.* The labels of $(g,k)$ in $M$ and in $M'$ are $d(x_i(k),x'_i(k))$ apart, because the action is isometric. By [relabelling the propagation](prop-relabel.md), the identity matrices have propagation at most this error, which tends to $0$. They are mutually inverse and self-transpose.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic duality](asymptotic-duality.md)
- [Unitary isomorphism](../l-theory/base/unitary-isomorphism.md)

## Proof depends on

- [Relabelling changes propagation](prop-relabel.md)
