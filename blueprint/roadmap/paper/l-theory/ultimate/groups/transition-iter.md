---
article_id: af_213f5451ae6aa1c9806e0760
declaration: def
origin: background
statement: formalized
lean: HSP.transitionIter
---

# Iterated transition

For $j,m\ge0$, the *iterated transition* $t^m:L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-m\rangle}_k(\mathcal A)$ is defined by $t^0=1$ and $t^{m+1}=t\circ t^m$, where $t:L^{\langle -j-m\rangle}_k(\mathcal A)\to L^{\langle -j-m-1\rangle}_k(\mathcal A)$ is the [lower transition map](../../localization/transitions/transition-lower.md).

## Sources

- New: composites of the transition maps of the sequence of lower L-groups.

## Depends on

- [Lower transition map](../../localization/transitions/transition-lower.md)
