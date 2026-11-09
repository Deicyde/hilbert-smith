---
article_id: af_2dc36290e148fc097e84abe4
declaration: lemma
origin: bridged
---
# Homotopic labellings have equal germs

If $c_0,c_1:T^n\to S^n$ are homotopic, then $\mathfrak m_{c_0}=\mathfrak m_{c_1}$. In particular this holds for homotopies relative to $\infty$; no condition on the exterior is needed.

*Proof sketch.*
1. Let $c:[0,1]\times T^n\to S^n$ be a homotopy. Let $W_i$ be the block $C(k_i)\otimes I_{k_i}\otimes P$, where the arc realizes $[0,1]$ with mesh $1/k_i$. Label each cell by $c$ at its centre.
2. [Block duality](../chain-models/blocks/block-duality.md) makes $(\partial W_i\to W_i)$ a strict Poincaré pair. Its propagation in $d_\infty$ on $T^n\times[0,1]$ is at most $h_i$, so its sphere propagation is at most $\omega_c(h_i)\to0$.
3. $\partial W_i=D_i\otimes[0]\oplus D_i\otimes[k_i]$, with structure $-s\varphi_i\oplus s\varphi_i$ for one sign $s$. The end labels are $c_0$ and $c_1$. So $(D_i,s\varphi_i)_{c_1}$ is cobordant to $(D_i,s\varphi_i)_{c_0}$, and their classes in $\mathbb L_N(\mathcal A_{\mathbf 1}(S^n))$ are equal ([cobordism](../l-theory/base/groups/l-group.md)). Multiply by $s$ and apply the quotient functor.

## Sources
- HS paper, Section 12 (scalar control homotopies). New: the cylinder is an exact block.
## Depends on
- [Germ](germ.md)
## Proof depends on
- [Block pair](../chain-models/blocks/block-pair.md), [block duality](../chain-models/blocks/block-duality.md), [L-groups](../l-theory/base/groups/l-group.md), [functoriality](../l-theory/ultimate/groups/induced-map-comp.md)
