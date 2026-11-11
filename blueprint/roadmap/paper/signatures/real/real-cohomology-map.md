---
article_id: af_b1b355904ff25db37af6a691
declaration: def
origin: background
statement: formalized
lean: HSP.realHco.map
---

# The map on real cohomology induced by a chain map

A chain map $f:C\to D$ of chain complexes in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ induces $f^*:H^r(D;\mathbb R)\to H^r(C;\mathbb R)$ on [real cohomology](real-cohomology.md), $[x]\mapsto[f_r^Tx]$, with the [real matrices](real-matrix.md) of the transposes $f_r^*$.

*Proof sketch.* (Well-definedness.) $f_r=e'_rf_re_r$, so $f_r^T$ maps $\mathrm{im}(e_r'^T)$ into $\mathrm{im}(e_r^T)$. Since $f$ commutes with the differentials, $f_r^T$ commutes with the coboundaries, so it maps cocycles to cocycles and coboundaries to coboundaries.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Real cohomology](real-cohomology.md)
- [The real matrix of a morphism](real-matrix.md)
