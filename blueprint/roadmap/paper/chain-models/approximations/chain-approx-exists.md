---
article_id: af_f022e376f56038bf29c126f9
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.ChainModels.exists_chainApprox
---
# Chain approximations exist

Let $E(k)\subseteq C(k)$ be spanned by the [far cubes](far-cubes.md), those whose closed cubes miss $\overline B(0,3/2)$. For $k\ge k_0$ and $L\in\mathcal F$, take the [approximation boxes](chain-approx-box.md) $\Gamma_L(c)=\mathrm{Box}_k(N_h(L|c|))$, with $h=4/k$ and $N_h$ the closed $d_\infty$-neighbourhood, a subcomplex of $C(k)$ [spanned by its cubes](../grid/grid-box-acyclic.md). On the [realization](../grid/realization.md) of $C(k)$, with its basis of cubes and the [realized augmentation](../grid/realized-augmentation.md) $\varepsilon$, this is a carrier, and $|\Gamma_L(c)|$ has $d_\infty$-diameter at most $\omega(h)+4h$ for every $c$. There is a chain map $a:C(k)\to C(k)$ whose realization is carried by $\Gamma_L$, with $a|_{E(k)}=1$ (every cube of $E(k)$ is fixed) and $\varepsilon a=\varepsilon$.

*Proof sketch.* $L|c|$ has $d_\infty$-diameter at most $\omega(h)$ by [properties](completed-maps-properties.md) (1), so $N_h(L|c|)$ is admissible in the sense of [box hull properties](../grid/box-hull-properties.md): it is nonempty, and each coordinate projection lies in a closed arc of length at most $\omega(h)+2h\le1$, by the choice of $k_0$ in the [mesh sequence](../grid/mesh-sequence.md). Box hull properties (1) give the nesting under faces and (2) the diameter bound; [boxes are acyclic](../grid/grid-box-acyclic.md). The far cubes span a [based subcomplex](../grid/based-subcomplex.md) $E(k)$: a cube occurring in $dc$ replaces one factor $e_w$ of $c$ by $[w]$ or $[w+1]$, an endpoint of the arc realizing $e_w$, so its closed cube lies in $|c|$ and is far when $c$ is. The identity on $E(k)$ is carried, because $L$ fixes $|c|$ and $c\in\mathrm{Box}_k(N_h(|c|))$ by box hull properties (3), and it preserves $\varepsilon$. Apply [carried chain maps](../grid/carriers/carried-chain-map.md) with $E'=E(k)$ and $\varepsilon_E=\varepsilon$.

## Sources
- New: replaces simplicial approximation (HS paper, Section 9).
## Depends on
- [Local datum](../../local-data/chart/local-datum.md)
- [The torus](../grid/torus.md)
- [Mesh start](../mesh/mesh-start.md)
- [The cube of a basis vector](../grid/cubical/grid-cell.md)
- [Augmentation of the grid complex](../grid/cubical/grid-aug.md)
- [The track family](maps/track-family.md)
- [Grid boxes](../grid/grid-box.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)
- [Far cubes](far-cubes.md), [approximation boxes](chain-approx-box.md), [realized augmentation](../grid/realized-augmentation.md)
- [Boxes are acyclic](../grid/grid-box-acyclic.md), [realization](../grid/realization.md), [modulus of the track family](modulus.md), [carriers](../grid/carriers/acyclic-carriers.md), [cubical torus grid](../grid/cubical/cubical-torus-grid.md)
## Proof depends on
- [The closed cube](../grid/cubical/grid-cube-realization.md)
- [Grid cubes](../grid/cubical/grid-cube.md)
- [Track maps](track-map.md), [mesh sequence](../grid/mesh-sequence.md)
- [Based subcomplexes](../grid/based-subcomplex.md)
- [Carried chain maps](../grid/carriers/carried-chain-map.md), [box hull properties](../grid/box-hull-properties.md), [properties](completed-maps-properties.md)
