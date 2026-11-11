---
article_id: af_35d70cce2896537b56048224
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.LocalDatum.isCompact_testMap_preimage
---

# Preimages under the test map

For a local datum, $0<\rho<\rho_+$ and every compact $C\subseteq\mathbb R^n$, the set $f^{-1}(C)$ is a compact subset of $U^+$.

*Proof sketch.* $K=\{x\in B(0,\rho):\sigma_\rho(x)\in C\}$ is the image of $C$ under the inverse homeomorphism of the pinch, so it is compact and lies in $B(0,\rho)$. Then $f^{-1}(C)$ is the set of points of $\overline B(0,\rho+D)$ at which $F_0$ lands in $K$, a closed subset of a compact ball inside $\Omega$, and it lies in $U^+$ because $\rho<\rho_+$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the compact sets $\mathcal K_v$ inside the interior of $Z^+$)

## Depends on

- [The test map](test-map.md)
- [The open test region](open-test-region.md)

## Proof depends on

- [The pinch opens the ball onto $\mathbb R^n$](pinch-homeomorph.md)
- [The averaged map is continuous](averaged-map-continuous.md)
- [The averaged map moves points little](averaged-map-displacement.md)
