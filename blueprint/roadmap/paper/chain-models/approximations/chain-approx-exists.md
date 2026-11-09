---
article_id: af_f022e376f56038bf29c126f9
declaration: lemma
origin: bridged
---
# Chain approximations exist

Let $E(k)\subseteq C(k)$ be spanned by the cubes whose closed cubes miss $\overline B(0,3/2)$. For $k\ge k_0$ and $L\in\mathcal F$, put $\Gamma_L(c)=\mathrm{Box}_k(N_h(L|c|))$. This is a carrier of $d_\infty$-diameter at most $\omega(h)+4h$. There is a chain map $a:C(k)\to C(k)$ carried by $\Gamma_L$, with $a|_{E(k)}=1$ and $\varepsilon a=\varepsilon$.

*Proof sketch.* $L|c|$ has diameter at most $\omega(h)$, so the hull is defined. Use box hull properties (1) and (2) and [boxes are acyclic](../grid/grid-box-acyclic.md). The identity on the subcomplex $E(k)$ is carried, because $L$ fixes $|c|$, and it preserves $\varepsilon$. Apply [carried chain maps](../grid/carried-chain-map.md) with $\varepsilon_E=\varepsilon$.

## Sources
- New: replaces simplicial approximation (HS paper, Section 9).
## Depends on
- [Box hull](../grid/box-hull.md), [track maps](track-map.md), [mesh sequence](../grid/mesh-sequence.md)
## Proof depends on
- [Carried chain maps](../grid/carried-chain-map.md), [box hull properties](../grid/box-hull-properties.md), [boxes are acyclic](../grid/grid-box-acyclic.md), [properties](completed-maps-properties.md)
