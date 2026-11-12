---
article_id: af_2be09f20d0d2885ed0277cbb
declaration: lemma
origin: background
---

# Evaluation is a perfect pairing

The [evaluation pairing](real-evaluation.md) $H^r(C;\mathbb R)\times H_r(C;\mathbb R)\to\mathbb R$ of a chain complex $C$ in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ is perfect. For a chain map $f:C\to D$, with the induced maps $f^*$ on [real cohomology](../real/real-cohomology-map.md) and $f_*$ on [real homology](real-homology-invariance.md), it satisfies $\langle f^*x,y\rangle=\langle x,f_*y\rangle$. Hence $\dim H^r=\dim H_r$, and $f^*$ and $f_*$ have equal rank.

*Proof sketch.* The pairing of $\mathrm{im}(e^T)$ with $\mathrm{im}(e)$ is perfect: if $\langle x,ez\rangle=0$ for all $z$, then $x=e^Tx=0$. So the cochain complex is the dual of the chain complex. Over a field, the cohomology of the dual complex is the dual of the homology. Naturality holds because $\langle f^Tx,y\rangle=\langle x,fy\rangle$. A linear map and its dual have the same rank.

## Sources

- [published: universal coefficients over a field] [U]

## Depends on

- [Real homology](real-homology.md)
- [The evaluation pairing](real-evaluation.md)
- [The map on real cohomology induced by a chain map](../real/real-cohomology-map.md)
- [Real homology is homotopy invariant](real-homology-invariance.md)
