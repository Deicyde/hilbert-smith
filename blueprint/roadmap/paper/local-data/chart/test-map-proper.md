---
article_id: af_35d70cce2896537b56048224
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.isCompact_testMap_preimage
---

# Preimages under the test map

For a local datum, $0<\rho<\rho_+$ and every compact $C\subseteq\mathbb R^n$, the set $f^{-1}(C)$ is a compact subset of $U^+$.

*Proof sketch.* $C$ is compact, hence closed in the compact Hausdorff space $S^n$, and $f$ is continuous, so $f^{-1}(C)$ is a closed subset of $S^n$ and therefore compact. If $f(x)\in C$ then $f(x)\ne\infty$, so $x\in\Omega$ and $\sigma_\rho(F_0(x))\ne\infty$, that is $|F_0(x)|<\rho<\rho_+$; hence $x\in U^+$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the compact sets $\mathcal K_v$ inside the interior of $Z^+$)

## Depends on

- [The test map](test-map.md)
- [The open test region](open-test-region.md)
- [Local datum](local-datum.md)

## Proof depends on

- [The test map is continuous](test-map-continuous.md)
- [The averaged chart map](averaged-map.md)
- [The pinch map](pinch.md)
