---
article_id: af_6c2e95378ca6bd02326c9773
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.compressed_d
---
# Compressed differential

For $i\ge i_0$, $\hat d\hat d=0$ and $\mathrm{pr}_i\,d=\hat d\,\mathrm{pr}_i$. For every $i$, $\hat d$ has [propagation](../categories/asymptotic/propagation.md) at most $\delta_i$, the [bound sequence](bound-sequence.md), for the labels of the [compressed complex](compressed-complex.md) in $T\times S^n$. So $(C,\hat d)$, with differentials [represented](compressed-rep.md) by $\hat d$, is a chain complex in $\mathcal A_{\mathbf 1}(T\times S^n)$, and $C_r$ is a zero object for $r\notin[0,N]$.

*Proof sketch.* $\mathrm{pr}\,d=\mathrm{pr}\,d(\mathrm{in}\,\mathrm{pr}+Q)=\hat d\,\mathrm{pr}$, because $\mathrm{pr}\,dQ=0$ ([discarded subcomplex](discarded-subcomplex.md)). Then $\hat d\hat d=(\hat d\,\mathrm{pr})\,d\,\mathrm{in}=\mathrm{pr}\,d^2\,\mathrm{in}=0$. For $i\ge i_0$, $\hat d$ is a submatrix of $d^{[u]}$, since retained cells lie in $\mathcal B_i(u)$ ([buffers](buffer-eventually.md) (1)); $d\in\mathcal P_i$ has type $0$, so buffers (3) bound its propagation by $\delta_i$ ([graph-type matrices](../corner/actions/graph-type.md)). For $i<i_0$, $\hat d=0$. $D_i$ is zero outside degrees $[0,N]$.

## Sources
- HS paper, Section 10.

## Depends on

- [Compressed complex](compressed-complex.md)
- [Compressed maps](compressed-maps.md)
- [Start index](start-index.md)
- [Bound sequence](bound-sequence.md)
- [Retained projection](retained-projection.md)
- [Morphisms represented by compressed matrices](compressed-rep.md)

## Proof depends on

- [The bound sequence is null](bound-sequence-null.md)
- [Discarded subcomplex](discarded-subcomplex.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Graph-type matrices](../corner/actions/graph-type.md)
