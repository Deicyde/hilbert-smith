---
article_id: af_1885db5a47125c28b80d3db7
declaration: def
origin: bridged
---
# Completed map

Fix a [local datum](../../local-data/chart/local-datum.md) and let $\theta(x)=\min(1,\max(0,3-2|x|))$. For $a\in\mathbb Z_p$ define $\widehat a(x)=x+\theta(x)(a\cdot x-x)$ when $|x|<2$, and $\widehat a(x)=x$ otherwise. Since $\widehat a$ is the identity off $\overline B(0,3/2)$, it induces a self-map of $T^n$ through the quotient $q:[-2,2]^n\to T^n$, also written $\widehat a$. The *completed representative* of $g\in G_i$ is $\widehat{r_i(g)}$, with $r_i$ as in [representatives](../../local-data/control/representative-map.md).

## Sources
- HS paper, Section 9 (completed maps).
## Depends on
- [Local datum](../../local-data/chart/local-datum.md)
- [Representatives](../../local-data/control/representative-map.md)
