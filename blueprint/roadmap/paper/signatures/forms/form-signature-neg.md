---
article_id: af_9fc0174e5df45998c7bb9390
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.formSign_neg
---

# Negation

$\mathrm{sign}_{-b}=-\mathrm{sign}_b$, for every bilinear form $b$ on a finite-dimensional real vector space $W$ and every action $\rho$ of a monoid $G$ on $W$ by linear maps.

*Proof sketch.* If $(V^+,V^-)$ is a splitting for $b$, then $(V^-,V^+)$ is a splitting for $-b$, and conversely. Apply [independence](../l-four/signature-splitting-independence.md). If $b$ has no splitting, neither has $-b$, and both sides are $0$.

## Sources

- New: immediate.

## Depends on

- [The equivariant signature](form-signature.md)

## Proof depends on

- [Independence](../l-four/signature-splitting-independence.md)
