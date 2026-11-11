---
article_id: af_bce3eb446866237d5a2535bf
declaration: def
origin: background
statement: formalized
lean: HSP.dualCx.mapHomotopyEquiv
---

# Duals of homotopy equivalences

Let $f:C\to D$ be a chain homotopy equivalence of complexes in a duality category $\mathcal B$, with homotopy inverse $g$ and homotopies $H:gf\simeq1$ and $H':fg\simeq1$, and let $n\in\mathbb Z$. The *dual homotopy equivalence* $D^{n-*}\to C^{n-*}$ has map the [dual](dual-complex.md) $f^{n-*}$, inverse $g^{n-*}$, and homotopies $f^{n-*}g^{n-*}\simeq1$ and $g^{n-*}f^{n-*}\simeq1$ obtained by dualizing $H$ and $H'$: $K_r=(-1)^{r+1}H^*_{n-r-1}$, and likewise with $H'$.

*Proof sketch.* (Proof obligation: the homotopy identities.) With $gf-1=dH+Hd$ and $fg-1=dH'+H'd$: dualizing $(dH+Hd)_{n-r}$ shows that $K_r=(-1)^{r+1}H^*_{n-r-1}:C^*_{n-r}\to C^*_{n-r-1}$ satisfies $f^{n-*}g^{n-*}-1=dK+Kd$ on $C^{n-*}$, because the differential of $C^{n-*}$ is $(-1)^rd^*$. The same formula with $H'$ gives $g^{n-*}f^{n-*}\simeq1$.

## Sources

- New: direct sign computation

## Depends on

- [Dual complex](dual-complex.md)
- [Dual of a chain map](functors/dual-map.md)

## Proof depends on

- [Duals of chain maps reverse composition](functors/dual-map-comp.md)
- [Duals of identity chain maps](functors/dual-map-id.md)
