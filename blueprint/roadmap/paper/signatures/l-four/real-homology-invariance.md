---
article_id: af_6108271b5c3d37f418571304
declaration: lemma
origin: background
---

# Real homology is homotopy invariant

A chain map $f:C\to D$ of complexes in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ induces $f_*:H_r(C;\mathbb R)\to H_r(D;\mathbb R)$ on [real homology](real-homology.md), $[y]\mapsto[f_ry]$, with the [real matrices](../real/real-matrix.md) of the $f_r$; this is compatible with composition and identities. If $f$ is a chain homotopy equivalence, $f_*$ is an isomorphism for every $r$.

*Proof sketch.* (Well-definedness.) $f_r=e'_rf_re_r$, so $f_r$ maps $\mathrm{im}(e_r)$ into $\mathrm{im}(e'_r)$. Since $f$ commutes with the differentials, it maps cycles to cycles and boundaries to boundaries. Real matrices multiply like the rational ones, which gives compatibility with composition and identities. (Invariance.) Base change to $\mathbb R$ is additive, so it carries the homotopy inverse and the homotopies to real ones. Homotopic maps induce the same map on homology.

## Sources

- [published: standard homological algebra] [U]

## Depends on

- [Real homology](real-homology.md)
- [The real matrix of a morphism](../real/real-matrix.md)
