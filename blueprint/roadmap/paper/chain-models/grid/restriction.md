---
article_id: af_35183c4bb25bc9ceeb9af456
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.restrict
---
# Buffered restriction of a matrix

For a real number $v$ let $\iota_v$ be the based inclusion of the span of the [buffered cells](buffered-cells.md) $\mathcal B_i(v)$ (in $D_i$ or in $D_i^{N-*}$) and $p_v$ the based projection onto it; these spans carry the [control labels](control-labels.md) $\lambda$. For radii $v,v'$ (in use $0<v\le v'$) and a matrix $u$ between such modules, the *restriction* is $u^{[v,v']}=p_{v'}u\,\iota_v$, and $u^{[v]}=u^{[v,v]}$. In matrix terms, $u^{[v,v']}$ keeps the rows of the buffered target cells and the columns of the buffered source cells.

## Sources
- HS paper, Section 9 (the eventual definition of target labels).
## Depends on
- [Buffered cells](buffered-cells.md), [control labels](control-labels.md)
