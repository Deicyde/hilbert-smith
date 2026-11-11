---
article_id: af_a88b852ee8021c00c4074099
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.bufferedCells
---
# Buffered cells

For a real number $v$ (in use $v>0$), the *buffered cells* $\mathcal B_i(v)$ are the cells $b$ of $D_i$, and their duals in $D_i^{N-*}$, whose [sphere label](../sphere-labels.md) $s_b$ is [buffered](buffered-sphere-labels.md) at radius $v$: $s_b\in B(0,v)$, the open Euclidean ball in $\mathbb R^n\subseteq S^n$. Membership depends on $s_b$ alone. More generally, for any set of cells $B$ (finiteness is not needed) with torus labels $x_b$, $\mathcal B(v)=\{b: f_T(x_b)\in B(0,v)\}$; for $D_i$ and $D_i^{N-*}$ this is $\mathcal B_i(v)$.

## Sources
- HS paper, Sections 9-10 (the buffered domain).
## Depends on
- [Sphere labels](../sphere-labels.md), [buffered sphere labels](buffered-sphere-labels.md)
