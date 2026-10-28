---
article_id: af_3a6f44637ad2d03d57ea2f3c
declaration: lemma
origin: background
---

# Symmetrization by averaging

Let $C$ be an additive category with an involutive duality
$(D, \varpi)$ as in
[Transpose involution and orthogonal sums](transpose-involution.md).
For $\alpha : X \to DX$, any half of $\alpha$ plus its transpose
is symmetric: if doubling is injective on $X \to DX$ (as when $2$
is invertible) and $\tau + \tau = \alpha + \alpha^t$, then
$\tau^t = \tau$.

Cited wherever a map is symmetrized by averaging with its
transpose: the symmetric cone averages the third map of a triangle
morphism with its signed transpose, halving the sum.

*Proof sketch.* Transposing $\tau + \tau = \alpha + \alpha^t$
gives $\tau^t + \tau^t = \alpha^t + \alpha^{tt}$ by additivity of
the transpose. Involution gives $\alpha^{tt} = \alpha$, so both
$\tau^t + \tau^t$ and $\tau + \tau$ equal
$\alpha^t + \alpha$; injectivity of doubling yields
$\tau^t = \tau$.

## Sources

- [Background map: `Balmer2000` §1](../../sources/background.md)

## Depends on

- [Transpose involution and orthogonal sums](transpose-involution.md)

## Proof depends on

- [Transpose involution and orthogonal sums](transpose-involution.md)
