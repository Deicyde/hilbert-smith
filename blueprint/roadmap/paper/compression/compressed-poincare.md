---
article_id: af_2d547e7264821dc49722c203
declaration: lemma
origin: bridged
---
# The compressed complex is Poincaré

Let $Z_0$ be the [exterior](../corner/exterior.md) for $n$ and the buffer radius $R$, and $Z=T\times Z_0$ for the control space $T$, possibly empty; $Z$ is closed and invariant ([the exterior is closed](../corner/exterior-closed.md)). Then $(C,\hat\varphi)$, with differential $\hat d$, is a [strict $N$-dimensional symmetric Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md) in the [exterior quotient](../categories/supports/exterior-quotient.md) $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$, whose chain objects are objects of $\mathcal B_{\mathbf 1,Z}(T\times S^n)$. A homotopy inverse of $\hat\varphi_\natural$ is $\hat b$, with homotopies $\hat H$ and $\hat H'$.

*Proof sketch.*
1. Morphisms. $\hat d$ has propagation at most $\delta_i$ ([compressed differential](compressed-differential.md)). For $i\ge i_0$, $\hat\varphi,\hat b,\hat H,\hat H'$ are submatrices of $w^{[u]}$ for type-$0$ elements $w\in\mathcal P_i$, because retained cells lie in $\mathcal B_i(u)$ ([buffers](buffer-eventually.md) (1)); so their propagation is at most $\delta_i$ by buffers (3). Since $\delta_i\to0$, all of them are morphisms of $\mathcal A_{\mathbf 1}(T\times S^n)$.
2. [Residuals](compressed-residuals.md) (4) give $\partial\hat\varphi=0$ and invariance under the involution, exactly.
3. In residuals (5)-(7), every word on the right is $p_2\alpha Q_1\beta\jmath_0$ with $\alpha,\beta$ of type $0$. By the [endpoint lemma](endpoint-lemma.md) it is $x\,y$ through $W_i$, with $x,y$ of propagation at most $\delta_i$ and every label of $W_i$ in $Z$. So the levelwise sums factor through an object of $\mathcal A_Z$ ([sums of witnesses](../corner/actions/witness-sum.md)), and they are zero in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$. Below $i_0$ all maps are zero, and morphisms are taken modulo eventual equality.
4. Hence $\hat b$ is a chain map, and $\hat\varphi_\natural\hat b\simeq1$, $\hat b\hat\varphi_\natural\simeq1$ through $\hat H,\hat H'$.

## Sources
- HS paper, Section 10 (compressed realization). New: symmetric over $\mathbb Q$, with no quadratic halving.

## Depends on

- [Compressed differential](compressed-differential.md)
- [Compressed maps](compressed-maps.md)
- [Strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Exterior](../corner/exterior.md)
- [The exterior is closed](../corner/exterior-closed.md)

## Proof depends on

- [Residuals](compressed-residuals.md)
- [Endpoint lemma](endpoint-lemma.md)
- [Buffers hold eventually](buffer-eventually.md)
- [Sums of witnesses](../corner/actions/witness-sum.md)
- [Support ideal](../categories/supports/support-ideal.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
