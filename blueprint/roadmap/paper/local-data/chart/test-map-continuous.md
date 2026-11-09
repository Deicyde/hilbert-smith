---
article_id: af_406386be11f6e0eb39596e1b
declaration: lemma
origin: bridged
---

# The test map is continuous

For a local datum and $0<\rho<\rho_+$, the test map $f$ is continuous.

*Proof sketch.* $f\ne\infty$ only on $\{x\in\Omega:|F_0(x)|<\rho\}\subseteq B(0,\rho+D)$, whose closure lies in $B(0,2)\subseteq\Omega$. So $f$ agrees with the continuous $\sigma_\rho\circ F_0$ on the open set $\Omega$, and with $\infty$ on the open set $S^n\setminus\overline B(0,\rho+D)$; these two open sets cover $S^n$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The test map](test-map.md)

## Proof depends on

- [The averaged map is continuous](averaged-map-continuous.md)
- [The averaged map moves points little](averaged-map-displacement.md)
- [The pinch is continuous](pinch-continuous.md)
