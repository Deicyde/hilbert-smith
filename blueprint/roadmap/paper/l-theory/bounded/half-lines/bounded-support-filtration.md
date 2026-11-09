---
article_id: af_f81108571cc1a2e75a0ba175
declaration: lemma
origin: cited
---

# Bounded support is a Karoubi filtration of a half-line

For $M\in H_\varepsilon$ and $R\in\mathbb N$, let $w_R$ be the diagonal idempotent of propagation $0$ that is $1$ in the degrees $|n|\le R$ and $0$ elsewhere. With $\mathcal D(M)=\{w_R:R\in\mathbb N\}$, $H_b\subset H_\varepsilon$ is an involution-invariant Karoubi filtration.

*Proof sketch.* The argument of [Half-lines are Karoubi filtrations](half-line-filtration.md) with the windows $\{|n|\le R\}$ in place of the half-lines. $w_R$ splits through the window truncation, which lies in $H_b$, and $1-w_R$ through the complementary truncation, which lies in $H_\varepsilon$ because $M$ does. A map of propagation $r$ out of or into an object of $H_b$ supported in $\{|n|\le R\}$ is fixed by $w_{R+r}$. $H_b$ is closed under isomorphism and duality as in that article.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Half-line subcategories](half-lines.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)

## Proof depends on

- [Half-lines are Karoubi filtrations](half-line-filtration.md)
