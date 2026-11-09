---
article_id: af_4857639783789f947085c969
declaration: def
origin: cited
---

# Transition map

For $j\ge0$ and $m\in\mathbb Z$, the transition map
$$t:L^p_m(C_{\mathbb Z^j}\mathcal A)\to L^p_{m+1}(C_{\mathbb Z^{j+1}}\mathcal A),\qquad [C,\phi]\mapsto[C\otimes\Lambda,\phi\otimes\lambda],$$
is a well-defined homomorphism. For $m=k+j$ it is a homomorphism $L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j-1\rangle}_k(\mathcal A)$.

*Proof sketch.*
1. Complexes. $(C\otimes\Lambda,\phi\otimes\lambda)$ is a strict $(m+1)$-dimensional symmetric Poincaré complex: its chain objects are zero objects outside $[0,m+1]$; $T(\phi\otimes\lambda)=\phi\otimes\lambda$ and $\partial(\phi\otimes\lambda)=0$ by [Product formulas](product-formulas.md), items 1 and 2; and $(\phi\otimes\lambda)_\natural=(\phi_\natural\otimes\lambda_\natural)\circ\Xi$ is an equivalence by items 4 and 5 and [The line is Poincaré](symmetric-line-poincare.md).
2. Cobordisms. A cobordism is a strict pair with boundary $(C\oplus C',\phi\oplus(-\phi'))$. [Product of a pair with the line](product-with-line.md) gives a strict pair with boundary $((C\oplus C')\otimes\Lambda,(\phi\oplus(-\phi'))\otimes\lambda)$. The canonical isomorphism $(C\oplus C')\otimes\Lambda\cong C\otimes\Lambda\oplus C'\otimes\Lambda$ carries this structure to $\phi\otimes\lambda\oplus(-\phi'\otimes\lambda)$, block by block, since $\boxtimes$ is bilinear. By [Pair transport](../../base/pairs/pair-transport.md) the product is a cobordism from $t$ of $C$ to $t$ of $C'$. So $t$ is well defined on cobordism classes.
3. Additivity. The same canonical isomorphism, with $\chi=0$ in [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md), gives $t([C,\phi]+[C',\phi'])=t[C,\phi]+t[C',\phi']$.
4. Levels. $L^{\langle -j\rangle}_k(\mathcal A)=L^p_{k+j}(C_{\mathbb Z^j}\mathcal A)$, and $k+j+1=k+(j+1)$.

## Sources

- [Ranicki 1992, §17](../../../../../sources/paper/ranicki-1992.md) [U]
- New: well-definedness from the product lemmas.

## Depends on

- [Projective L-group](../../base/groups/l-group.md)
- [Group structure on L^p](../../base/groups/l-group-add.md)
- [External product with a complex over the line](external-product.md)
- [The symmetric line](symmetric-line.md)
- [Lower L-group](../../ultimate/groups/lower-l-group.md)

## Proof depends on

- [Product formulas](product-formulas.md)
- [The line is Poincaré](symmetric-line-poincare.md)
- [Product of a pair with the line](product-with-line.md)
- [Pair transport](../../base/pairs/pair-transport.md)
- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
