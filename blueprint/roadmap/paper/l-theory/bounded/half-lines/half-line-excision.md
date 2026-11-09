---
article_id: af_e2d9b6683b617a2e2466b79d
declaration: lemma
origin: cited
---

# Half-line excision

For the [inclusion of the half-line quotient](half-line-quotient-inclusion.md) $e$ and the [truncation](half-line-truncation.md) $\tau$, there are unitary natural isomorphisms $\eta:\mathrm{id}_{H_+/H_b}\cong\tau e$ and $\varepsilon:e\tau\cong\mathrm{id}_{C_\mathbb Z(D)/H_-}$, where $\eta_M$ is the class of the projection $M\to M_{\ge0}$ and $\varepsilon_M$ is the class of the inclusion $M_{\ge0}\to M$.

*Proof sketch.* Projection followed by inclusion is $1-\pi_{<0}$, and inclusion followed by projection is $1$. For $M\in H_+$ the summand $M_{<0}$ lies in $H_b$, so $\eta_M$ is invertible mod $H_b$. For every $M$, $M_{<0}$ lies in $H_-$, so $\varepsilon_M$ is invertible mod $H_-$. Naturality: for $f$ of propagation $r$, the two composites differ by the entries of $f$ between degrees $n<0$ and $m\ge0$, which pass through the degrees $[-r,-1]$, an object of $H_b$. Unitarity: the dual of the projection is the inclusion in degrees $n\ge0$, so $\eta_M^*\xi^\tau_M\eta_{M^*}$ is $1-\pi_{<0}$ on $M^*$, which is $1$ mod $H_b$; likewise $\varepsilon_M^*\varepsilon_{M^*}$ equals $\xi^{e\tau}_M$ mod $H_-$. In degrees $n<0$ every entry involved is a map between zero objects or passes through $M_{<0}$.

## Sources

- [Carlsson-Pedersen 1995, excision](../../../../../sources/paper/carlsson-pedersen-1995.md) [U]

## Depends on

- [Inclusion of the half-line quotient](half-line-quotient-inclusion.md)
- [Truncation to the positive half-line](half-line-truncation.md)
- [Unitary natural isomorphism](../../base/categories/unitary-isomorphism.md)
