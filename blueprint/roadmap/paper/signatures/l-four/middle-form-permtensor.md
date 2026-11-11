---
article_id: af_5f5e114bf4922737c86c8663
declaration: lemma
origin: bridged
---

# Middle form of a permutation tensor

Let $X$ be a finite $G$-set and $(C,\varphi)$ a strict 4-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$, and let $\tau_X$ be [tensoring with the permutation module](../point-functors/permutation-tensor.md). There is a $G$-equivariant isometric isomorphism $\mathbb R[X]\otimes H^2(C;\mathbb R)\to H^2(\tau_XC;\mathbb R)$ from $s_X\otimes b_C$ to $b_{\tau_XC}$, where $s_X$ is the standard form on $\mathbb R[X]$ and $G$ acts diagonally on the source.

*Proof sketch.* Let $\beta:G\times(X\times\{1..n\})\to X\times(G\times\{1..n\})$, $\beta(g,(x,k))=(gx,g,k)$, be the equivariant bijection that defines $\tau_X$, and $P_\beta$ the permutation matrix that reindexes along it. On $C_r=(n_r,e_r)$, $\tau_X(e_r)$ is $1_X\otimes e_r$ reindexed along $\beta$, and the same holds for $d$ and $\varphi_2$, since $(\tau_X)_\%\varphi$ applies $\tau_X$ to each component. So $P_\beta$ carries the real cochains of $\tau_XC$, with coboundary and $\varphi_2$, onto $\mathbb R[X]\otimes\mathrm{im}(e_r^T)$ with $1\otimes d^T$ and $1\otimes\varphi_2$. The functor $\mathbb R[X]\otimes-$ is exact, so $u\otimes[y]\mapsto[P_\beta^{-1}(u\otimes y)]$ is an isomorphism on $H^2$. $P_\beta$ is orthogonal, and the standard pairing on $\mathbb R^{X\times(G\times\{1..n_2\})}$ is the product of the standard pairings, so $b_{\tau_XC}$ corresponds to $s_X\otimes b_C$. The map is equivariant because $\beta$ is.

## Sources

- HS paper, Section 3

## Depends on

- [The middle form](middle-form.md)
- [Tensoring with a permutation module](../point-functors/permutation-tensor.md)

## Proof depends on

- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
