---
article_id: af_ab837784884798312a6405d4
declaration: lemma
origin: bridged
---

# Dual form of the pair map

Let $(f:C\to D,\delta\phi,\phi)$ be a strict $n$-dimensional Poincaré pair with [pair map](pair-map.md) $\psi$. Let $\varepsilon:(D^{n-*})^{n-*}\to D$ be $\varepsilon_r=(-1)^{r(n-r)}$, and write $\psi^\flat=\varepsilon\circ\psi^{n-*}:\mathcal C(f)^{n-*}\to D$. Then $\psi^\flat$ is a chain homotopy equivalence, and on $\mathcal C(f)^*_{n-r}=D^*_{n-r}\oplus C^*_{n-r-1}$ its components are $\psi^\flat_r=(\delta\phi_r,\ (-1)^nf\phi_r)$.

*Proof sketch.* (1) $\varepsilon$ is a chain isomorphism, since the differential of the double dual is $(-1)^{n+1}d$ and the signs $(-1)^{r(n-r)}$ absorb it. (2) The components: $(\psi^{n-*})_r$ is the transpose of $\psi_{n-r}=(\delta\phi_{n-r},(-1)^{n-r}\phi_{n-r-1}f^*)$, and $T\delta\phi=\delta\phi$, $T\phi=\phi$ turn the transposes, multiplied by $(-1)^{r(n-r)}$, into $\delta\phi_r$ and $(-1)^nf\phi_r$. (3) $\psi^{n-*}$ is an equivalence by [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md), and composing with the isomorphism $\varepsilon$ keeps it one.

## Sources

- New: sign computation

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Dual complex](../complexes/dual-complex.md)
- [Pair map](pair-map.md)

## Proof depends on

- [Duals of homotopy equivalences](../complexes/dual-homotopy-equivalence.md)
- [T is an involution](../complexes/structure-involution-square.md)
