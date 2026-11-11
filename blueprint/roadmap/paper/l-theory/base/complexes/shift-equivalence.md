---
article_id: af_b19812d72923ec75460886cb
declaration: lemma
origin: background
---

# Shifts of homotopy equivalences

For a chain map $h:C'\to C$, let $\Sigma h:\Sigma C'\to\Sigma C$ be $h_{r-1}$ on the summand $C'_{r-1}$ of $(\Sigma C')_r$, with $\Sigma$ the shift of [Mapping cone](cone.md). If $h$ is a chain homotopy equivalence, then so is $\Sigma h$.

*Proof sketch.* The differential of $\Sigma C$ is $d$ on the summand $C_{r-1}$, with no sign. So $\Sigma h$ is a chain map, $\Sigma(gh)=\Sigma g\,\Sigma h$, $\Sigma1=1$, and a homotopy $H$ with $gh-1=dH+Hd$ gives the homotopy $(\Sigma H)_r=H_{r-1}$ with $\Sigma g\,\Sigma h-1=d\,\Sigma H+\Sigma H\,d$. Apply this to both composites of $h$ and a homotopy inverse.

## Sources

- New: direct

## Depends on

- [Mapping cone](cone.md)
