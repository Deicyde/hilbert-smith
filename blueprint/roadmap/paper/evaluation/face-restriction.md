---
article_id: af_615384191925b26d3309b000
declaration: lemma
origin: background
---
# Face restriction

Let $Q$ be a [block](../chain-models/blocks/block-pair.md) with an arc factor $F_j=I_m$, and let $F$ be the block obtained from $Q$ by replacing $F_j$ with the point factor at its top vertex $[m]$. Then $F$ is a based subcomplex of $\partial Q$; let $\iota$ and $p$ be its inclusion and projection. Then
$$p\,d_{\partial Q}\,\iota=d_F,\qquad p\,\varphi_{\partial Q}\,p^*=(-1)^{a_j}\varphi_F ,$$
where $a_j$ is the number of circle and arc factors before $F_j$.

*Proof sketch.*
1. $F$ is spanned by the cells of $\partial Q$ whose $j$-th factor is $[m]$, and $d[m]=0$ in $I_m$, so $F$ is closed under $d$.
2. $\varphi_{\partial Q}=\sum_{F_k\text{ arc}}(-1)^{a_k}(\kappa_k)_\%\varphi_{Q_k}$. For $k\ne j$, the $j$-th factor of $\varphi_{Q_k}$ is $\varphi_I$, which sends the vertex cochain $[m]^*$ to $\tfrac12e_{m-1}$, an edge; so $p(\kappa_k)_\%\varphi_{Q_k}p^*=0$.
3. For $k=j$, the $j$-th factor is $\varphi_C$ with $\varphi_C([m]^*)=+[m]$ ([arc pair](../chain-models/blocks/arc-pair.md)), which is the point structure $1$ after $p$. Both $\varphi_C$ restricted to $[m]$ and the point factor have degree and dimension $0$, so the block signs $(-1)^{q(p+m)}$ of the iterated product agree, and $p(\kappa_j)_\%\varphi_{Q_j}p^*=\varphi_F$.

## Sources
- New.
## Depends on
- [Block pair](../chain-models/blocks/block-pair.md)
## Proof depends on
- [Arc pair](../chain-models/blocks/arc-pair.md), [external product of structures](../l-theory/localization/products/external-product.md)
