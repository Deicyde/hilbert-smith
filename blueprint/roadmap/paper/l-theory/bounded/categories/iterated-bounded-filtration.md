---
article_id: af_4496a9accf718111952d4757
declaration: def
origin: cited
statement: formalized
lean: HSP.Bounded.powKaroubiFiltration
---

# Iterated bounded filtrations

Let $\mathcal U\subset\mathcal A$ be an [involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md). For every $j\ge0$, $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ is an involution-invariant Karoubi filtration, with the [iterated bounded categories](iterated-bounded-category.md).

*Proof sketch.* Induction on $j$; the case $j=0$ is the hypothesis. For the step apply [Bounded Karoubi filtrations](bounded-karoubi-filtration.md) to $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$, since $C_{\mathbb Z^{j+1}}=C_\mathbb ZC_{\mathbb Z^j}$.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]
- New: the induction from the one-step statement.

## Depends on

- [Iterated bounded subcategories are closed under sums and duals](iterated-bounded-sub-additive.md)
- [Iterated bounded subcategories](iterated-bounded-sub.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
- [Iterated bounded categories](iterated-bounded-category.md)

## Proof depends on

- [Bounded Karoubi filtrations](bounded-karoubi-filtration.md)
