---
article_id: af_9d25ea1bc86cbb3db26d016f
declaration: lemma
origin: cited
---

# Half-lines are Karoubi filtrations

For an object $M$ of $C_\mathbb Z(D)$ and $R\in\mathbb N$, let $p_R$ be the diagonal idempotent of propagation $0$ that is $1$ in the degrees with $\varepsilon n\ge-R$ and $0$ elsewhere. With $\mathcal D(M)=\{p_R:R\in\mathbb N\}$, $H_\varepsilon\subset C_\mathbb Z(D)$ is an involution-invariant Karoubi filtration.

*Proof sketch.*
1. $H_\varepsilon$ is full and additive. It is closed under the duality, since the dual of a zero object is a zero object.
2. $p_R$ splits through the truncation $M_{\{\varepsilon n\ge-R\}}$ (the degrees $\varepsilon n<-R$ replaced by a zero object), which lies in $H_\varepsilon$, and $1-p_R$ splits through the complementary truncation. The $p_R$ increase with $R$, so $\mathcal D(M)$ is directed.
3. Factorization. If $V\in H_\varepsilon$ has $V_m$ a zero object for $\varepsilon m<-R$ and $g:V\to M$ has propagation $r$, then $p_{R+r}g=g$. Likewise $hp_{R+r}=h$ for $h:M\to V$ of propagation $r$.
4. Duality. $p_R^*$ on $M^*$ is the $p_R$ of $M^*$.

## Sources

- [Carlsson-Pedersen 1995, §1](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Half-line subcategories](half-lines.md)
- [Involution-invariant Karoubi filtration](../../base/categories/karoubi-filtration.md)
