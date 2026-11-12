---
article_id: af_6c2e95378ca6bd02326c9773
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.Compression.compressed_d
---
# Compressed differential

For $i\ge i_0$, $\hat d\hat d=0$ and $\mathrm{pr}_i\,d=\hat d\,\mathrm{pr}_i$. For every $i$, $\hat d$ has [propagation](../categories/asymptotic/propagation.md) at most $\delta_i$, the [bound sequence](bound-sequence.md), for the labels of the [compressed complex](compressed-complex.md) in $T\times S^n$. So $(C,\hat d)$, with differentials [represented](compressed-rep.md) by $\hat d$, is a chain complex in $\mathcal A_{\mathbf 1}(T\times S^n)$, and $C_r$ is a zero object for $r\notin[0,N]$.

*Proof sketch.* $\mathrm{pr}\,d=\mathrm{pr}\,d(\mathrm{in}\,\mathrm{pr}+Q)=\hat d\,\mathrm{pr}$, because $\mathrm{pr}\,dQ=0$ ([discarded subcomplex](discarded-subcomplex.md)). Then $\hat d\hat d=\mathrm{pr}\,d\,(\mathrm{in}\,\mathrm{pr})\,d\,\mathrm{in}=\mathrm{pr}\,d^2\,\mathrm{in}-\mathrm{pr}\,dQ\,d\,\mathrm{in}=0$.

Propagation. For $i<i_0$, $\hat d=0$ and $\delta_i=0$. For $i\ge i_0$, the entry of $\hat d$ at a pair of compressed cells is the entry of $d$ at the corresponding retained cells. Retained cells lie in $\mathcal B_i(t')\subseteq\mathcal B_i(u)$ ([buffer conditions](buffer-conditions.md) (1), which hold from the [start index](start-index.md) on), and the label of a compressed cell is its [control label](../chain-models/grid/buffers/control-labels.md), which does not depend on the buffer radius. So every nonzero entry of $\hat d$ is a nonzero entry of $d^{[u]}$. The differential of $D_i$ lies in the [family](../chain-models/approximations/chain-model-family.md) $\mathcal P_i$ with type $0$, so by buffer condition (3) its restriction has [graph type](../corner/actions/graph-type.md) $0$ with bound $\delta_i$: since $0\cdot\lambda=\lambda$, the labels of every nonzero entry are within $\delta_i$ of each other. The [propagation](../categories/asymptotic/propagation.md) is the largest such distance over the nonzero entries, so it is at most $\delta_i$; as $\delta_i\ge0$, this holds even when $\hat d=0$.

The complex. The sequences $(\hat d_i)$ have propagation tending to zero ([the bound sequence is null](bound-sequence-null.md)), so they are morphisms of the [asymptotic category](../categories/asymptotic/asymptotic-category.md), and $\hat d\hat d=0$ for $i\ge i_0$ gives $d^2=0$ on classes ([equality of classes](../categories/asymptotic/structure/class-eq.md)). For $r\notin[0,N]$, $D_i$ has no cells in degree $r$: a [tensor product of based complexes](../chain-models/grid/based-complex-tensor.md) concentrated in $[0,a]$ and $[0,b]$ is concentrated in $[0,a+b]$, the [cubical torus grid](../chain-models/grid/cubical/cubical-torus-grid.md) is concentrated in $[0,n]$ (the [unit complex](../chain-models/grid/cubical/unit-complex.md) in degree $0$, the [circle complex](../chain-models/grid/cubical/circle-complex.md) in $[0,1]$), and [the complex of $\mathbb{CP}^2$](../chain-models/grid/cp2/cp2-complex.md) in $[0,4]$. So $C_r$ has rank $0$ at every level and is a zero object.

## Sources
- HS paper, Section 10.

## Depends on

- [Fixed local data](../local-data/control/fixed-local-data.md)
- [The control space](../local-data/control/control-space.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Compressed complex](compressed-complex.md)
- [Compressed maps](compressed-maps.md)
- [Start index](start-index.md)
- [Bound sequence](bound-sequence.md)
- [Retained projection](retained-projection.md)
- [Morphisms represented by compressed matrices](compressed-rep.md)
- [Propagation](../categories/asymptotic/propagation.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The round sphere](../corner/round-sphere.md)

## Proof depends on

- [Retained inclusion](retained-inclusion.md)
- [Projection onto the discarded cells](discard-projection.md)
- [The bound sequence is null](bound-sequence-null.md)
- [Discarded subcomplex](discarded-subcomplex.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Retained cells](retained-cells.md)
- [The family of chain-model matrices](../chain-models/approximations/chain-model-family.md)
- [Buffered cells](../chain-models/grid/buffers/buffered-cells.md)
- [Control labels](../chain-models/grid/buffers/control-labels.md)
- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [Free category of a finite group](../categories/asymptotic/free-category.md)
- [Equality of classes](../categories/asymptotic/structure/class-eq.md)
- [Tensor product of based complexes](../chain-models/grid/based-complex-tensor.md)
- [Cubical torus grid](../chain-models/grid/cubical/cubical-torus-grid.md)
- [The unit complex](../chain-models/grid/cubical/unit-complex.md)
- [The circle complex](../chain-models/grid/cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](../chain-models/grid/cubical/circle-dim-neg.md)
- [The cellular chain complex of CP^2](../chain-models/grid/cp2/cp2-complex.md)
- [The cells of CP^2 vanish in negative degrees](../chain-models/grid/cp2/cp2-dim-neg.md)
- [Local datum](../local-data/chart/local-datum.md)
- [Group sequence](../categories/asymptotic/group-sequence.md)
