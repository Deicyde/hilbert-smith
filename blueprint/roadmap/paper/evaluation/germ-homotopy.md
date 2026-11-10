---
article_id: af_2dc36290e148fc097e84abe4
declaration: lemma
origin: bridged
---
# Homotopic labellings have equal classes

If $c_0,c_1:\mathbb T^n\to S^n$ are homotopic, then $\mathfrak m_{c_0}=\mathfrak m_{c_1}$, for the [labelled-model class](germ.md).

*Proof sketch.*
1. Let $c:\mathbb T^n\times[0,1]\to S^n$ be a homotopy. Let $W_i$ be the [block](../chain-models/blocks/block-pair.md) $C(k_i)\otimes I_{k_i}\otimes P$ ($n$ circle factors, one arc factor realizing $[0,1]$ with mesh $1/k_i$, then $P$), and label each cell by $c$ at its centre. Since $c$ is uniformly continuous, these labels satisfy the hypothesis of [block duality](../chain-models/blocks/block-duality.md) (6), so $(\partial W_i\to W_i,\varphi_{W_i},\varphi_{\partial W_i})_i$ is a strict $(N+1)$-dimensional pair in $\mathcal A_{\mathbf 1}(S^n)$.
2. $\partial W_i=D_i\otimes[0]\oplus D_i\otimes[k_i]$, and since the arc is preceded by $n$ circles, $\varphi_{\partial W_i}=-s\varphi_i\oplus s\varphi_i$ with $s=(-1)^n$ ([block pair](../chain-models/blocks/block-pair.md), item 4, with $\varphi_C([0]^*)=-[0]$ and $\varphi_C([k_i]^*)=[k_i]$ from the [arc pair](../chain-models/blocks/arc-pair.md)). The end labels are $c_0$ and $c_1$ at the cell centres, which are the labels of the [labelled models](labelled-model.md) for $c_0$ and $c_1$.
3. So $(D_i,s\varphi_i)_{c_1}\oplus(D_i,-s\varphi_i)_{c_0}$ bounds, and $[D_i,s\varphi_i]_{c_1}=[D_i,s\varphi_i]_{c_0}$ in $L^p_N(\mathcal A_{\mathbf 1}(S^n))$ ([L-groups](../l-theory/base/groups/l-group.md), [negation](../l-theory/base/groups/l-group-neg.md), after the completion functor). Multiply by $s$, apply $\mathrm{cls}$ ([ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)) and the map induced by the quotient functor.

## Sources
- HS paper, Section 12 (homotopies of the scalar labelling). New: the cylinder is an exact block, and no condition relative to $\infty$ is needed.
## Depends on
- [Labelled-model class](germ.md)
## Proof depends on
- [Block pair](../chain-models/blocks/block-pair.md), [block duality](../chain-models/blocks/block-duality.md), [arc pair](../chain-models/blocks/arc-pair.md), [labelled model](labelled-model.md), [L-groups](../l-theory/base/groups/l-group.md), [negation in L](../l-theory/base/groups/l-group-neg.md), [ultimate L-group and cls](../l-theory/ultimate/groups/ultimate-l-group.md), [functoriality](../l-theory/ultimate/groups/induced-map-comp.md)
