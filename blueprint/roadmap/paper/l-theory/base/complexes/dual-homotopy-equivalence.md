---
article_id: af_bce3eb446866237d5a2535bf
declaration: lemma
origin: background
---

# Duals of homotopy equivalences

If $f:C\to D$ is a chain homotopy equivalence of complexes in a duality category $\mathcal B$, then for every $n\in\mathbb Z$ the [dual](dual-complex.md) $f^{n-*}:D^{n-*}\to C^{n-*}$ is a chain homotopy equivalence.

*Proof sketch.* Let $g$ be a homotopy inverse, with $gf-1=dH+Hd$ and $fg-1=dH'+H'd$. Then $g^{n-*}$ is a homotopy inverse of $f^{n-*}$: dualizing $(dH+Hd)_{n-r}$ shows that $K_r=(-1)^{r+1}H^*_{n-r-1}:C^*_{n-r}\to C^*_{n-r-1}$ satisfies $f^{n-*}g^{n-*}-1=dK+Kd$ on $C^{n-*}$, because the differential of $C^{n-*}$ is $(-1)^rd^*$. The same formula with $H'$ gives $g^{n-*}f^{n-*}\simeq1$.

## Sources

- New: direct sign computation

## Depends on

- [Dual complex](dual-complex.md)
