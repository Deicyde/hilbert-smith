---
article_id: af_27adeedb2df1e6985ac5f8d9
declaration: def
origin: background
---
# Block pair

A *block* is $Q=F_1\otimes\dots\otimes F_\ell\otimes P$, the iterated [tensor product of complexes](../../l-theory/localization/products/complex-product.md) for the pairing [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md) (from the left, with the tensor differential $d\otimes1+(-1)^p1\otimes d$, and bases enumerated as in the [cubical torus grid](../grid/cubical/cubical-torus-grid.md)), where each factor $F_j$ is a circle $S_k$, an arc $I_m$ with $m\ge1$ ([arc pair](arc-pair.md)), or a point: the complex $\mathbb Q[w]$ in degree $0$. Each circle or arc factor has its own mesh. Let $a_j$ be the number of circle and arc factors among $F_1,\dots,F_{j-1}$, and $N_Q=a_{\ell+1}+4$. The factor structures are $\varphi_{F_j}=\varphi^s$ ([circle duality](../grid/circle-duality.md)) for a circle, $\varphi_I$ for an arc, and $1\in M(\mathbb Q[w])_0$ for a point; their factor maps $b_{F_j}$ are $b$, the arc's $b$, and $1$.

1. The *boundary* $\partial Q$ is spanned by the cells having an endpoint vertex in some arc factor; $j:\partial Q\to Q$ is the based inclusion and $\pi:Q\to Q/\partial Q$ the based projection onto the other cells.
2. For an arc factor $F_j=I_m$, the *face* $Q_j$ is $Q$ with $F_j$ replaced by its boundary $C_j=\mathbb Q[0]\oplus\mathbb Q[m]$, with based inclusion $\kappa_j:Q_j\to\partial Q$.
3. $\varphi_Q\in M(Q)_{N_Q}$ is the iterated [external product](../../l-theory/localization/products/external-product.md) $\varphi_{F_1}\otimes\dots\otimes\varphi_{F_\ell}\otimes\varphi_P$, with the block signs $(-1)^{q(p+m)}$ used for the [chain-model duality](../grid/chain-model-duality.md). $\varphi_{Q_j}\in M(Q_j)_{N_Q-1}$ is the same product with $\varphi_{C_j}$ in place of $\varphi_{F_j}$.
4. $\varphi_{\partial Q}=\sum_{F_j\text{ arc}}(-1)^{a_j}(\kappa_j)_\%\varphi_{Q_j}\in M(\partial Q)_{N_Q-1}$, with the [pushforward](../../l-theory/base/complexes/structure-push.md).
5. The *block pair* is $(j:\partial Q\to Q,\varphi_Q,\varphi_{\partial Q})$, in the form of a [strict pair](../../l-theory/base/pairs/poincare-pair.md).
6. Its relative data are $\theta_Q=\varphi_Q\pi^*:(Q/\partial Q)^{N_Q-*}\to Q$ and $b_Q=\Xi_Q^{-1}\circ(b_{F_1}\otimes\dots\otimes b_{F_\ell}\otimes b_P)$, where $Q/\partial Q$ is identified with $\bigotimes_j(F_j/C_j)\otimes P$ ($C_j$ is zero for a circle or a point) and $\Xi_Q:(Q/\partial Q)^{N_Q-*}\to\bigotimes_j(F_j/C_j)^{\dim F_j-*}\otimes P^{4-*}$ is the iterated [dual of a tensor product](../../l-theory/localization/products/product-dual-iso.md).
7. The fundamental chain is $z_Q=z_{F_1}\otimes\dots\otimes z_{F_\ell}\otimes e_4$, with $z_{F}=\sum_we_w$ for a circle or an arc and $z_F=[w]$ for a point.

## Sources
- [Ranicki 1980, products of pairs](../../../../sources/paper/ranicki-1980.md) [U]. New: the exact cubical formulas.
## Depends on
- [Arc pair](arc-pair.md), [circle duality](../grid/circle-duality.md), [cells of CP^2](../grid/cp2-cells.md), [chain-model duality](../grid/chain-model-duality.md), [external product of structures](../../l-theory/localization/products/external-product.md), [dual of a tensor product](../../l-theory/localization/products/product-dual-iso.md), [pushforward of structures](../../l-theory/base/complexes/structure-push.md), [strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md), [tensor product of complexes](../../l-theory/localization/products/complex-product.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md), [cubical torus grid](../grid/cubical/cubical-torus-grid.md)
