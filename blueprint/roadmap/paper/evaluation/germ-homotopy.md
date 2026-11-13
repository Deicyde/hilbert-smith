---
article_id: af_2dc36290e148fc097e84abe4
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.Evaluation.germ_eq_of_homotopic
---
# Homotopic labellings have equal classes

If $c_0,c_1:\mathbb T^n\to S^n$ are homotopic, then $\mathfrak m_{c_0}=\mathfrak m_{c_1}$, for the [labelled-model class](germ.md).

*Proof sketch.*
1. Let $c:\mathbb T^n\times[0,1]\to S^n$ be a homotopy. Let $W_i$ be the [block](../chain-models/blocks/block-pair.md) $C(k_i)\otimes I_{k_i}\otimes P$ ($n$ circle factors, one arc factor realizing $[0,1]$ with mesh $1/k_i$, then $P$), and label each cell by $c$ at its centre. Since $c$ is uniformly continuous, these labels satisfy the hypothesis of [block pairs in the asymptotic category](../chain-models/blocks/block-pair-asymptotic.md) for $X=S^n$, so $(\partial W_i\to W_i,\varphi_{W_i},\varphi_{\partial W_i})_i$ is a strict $(N+1)$-dimensional pair in $\mathcal A_{\mathbf 1}(S^n)$.
2. $\partial W_i=D_i\otimes[0]\oplus D_i\otimes[k_i]$, and since the arc is preceded by $n$ circles, $\varphi_{\partial W_i}=-\nu\varphi_i\oplus\nu\varphi_i$ with $\nu=(-1)^n$, the $c_0$ summand first ([block pair](../chain-models/blocks/block-pair.md), item 4, with $\varphi_C([0]^*)=-[0]$ and $\varphi_C([k_i]^*)=[k_i]$ from the [arc pair](../chain-models/blocks/arc-pair.md)). The end labels are $c_0$ and $c_1$ at the cell centres, which are the labels of the [labelled models](labelled-model.md) for $c_0$ and $c_1$.
3. Put $C=(D_i,-\nu\varphi_i)_{c_0}$ and $C'=(D_i,-\nu\varphi_i)_{c_1}$, with $\phi'=-\nu\varphi_i$. The boundary of step 2 is $(C\oplus C',(-\nu\varphi_i)\oplus(-\phi'))$ in this order, so the pair is a [cobordism](../l-theory/base/pairs/cobordism.md) from $C$ to $C'$ with no reordering. The [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md) is a [strict duality functor](../l-theory/base/categories/duality-functors/karoubi-embedding-strict.md), so it carries this pair to a cobordism in $\mathrm{Kar}\,\mathcal A_{\mathbf 1}(S^n)$ ([duality functors carry pairs to pairs](../l-theory/base/pairs/functor-pair.md)). Hence $[D_i,-\nu\varphi_i]_{c_0}=[D_i,-\nu\varphi_i]_{c_1}$ in $L^p_N(\mathcal A_{\mathbf 1}(S^n))$ ([L-groups](../l-theory/base/groups/l-group.md)), and by [negation](../l-theory/base/groups/l-group-neg.md), applied when $-\nu=-1$, $[D_i,\varphi_i]_{c_0}=[D_i,\varphi_i]_{c_1}$. Apply $\mathrm{cls}$ ([the class map](../l-theory/ultimate/groups/ultimate-cls.md)) and the map induced by the quotient functor.

## Sources
- HS paper, Section 12 (homotopies of the scalar labelling). New: the cylinder is an exact block, and no condition relative to $\infty$ is needed.
## Depends on
- [Labelled-model class](germ.md)
## Proof depends on
- [Block pair](../chain-models/blocks/block-pair.md)
- [Block pairs in the asymptotic category](../chain-models/blocks/block-pair-asymptotic.md)
- [Arc pair](../chain-models/blocks/arc-pair.md)
- [Labelled model](labelled-model.md)
- [Cobordism](../l-theory/base/pairs/cobordism.md)
- [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md)
- [The Karoubi embedding is strict](../l-theory/base/categories/duality-functors/karoubi-embedding-strict.md)
- [Duality functors carry pairs to pairs](../l-theory/base/pairs/functor-pair.md)
- [L-groups](../l-theory/base/groups/l-group.md)
- [Negation in L](../l-theory/base/groups/l-group-neg.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Functoriality](../l-theory/ultimate/groups/induced-map-comp.md)
