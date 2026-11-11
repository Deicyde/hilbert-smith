---
article_id: af_cc5556435173cb9c35f10655
declaration: def
origin: bridged
---

# Forgetting the group

For each finite group $G$ fix once a bijection $\varepsilon_G:G\to\{0..|G|-1\}$. For $n\in\mathbb N$ the *group enumeration* is the bijection
$$e^G_n:G\times\{1..n\}\to\{1..|G|\,n\},\qquad e^G_n(g,k)=\varepsilon_G(g)\,n+k.$$

$U:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf 1}(X)$ is the strict duality functor sending $(n_i,x_i)$ to $(|G_i|\,n_i,\ \lambda_i\circ(e^{G_i}_{n_i})^{-1})$, so the generator $e^{G_i}_{n_i}(g,k)$ carries the label $\lambda_i(g,k)=\chi_i(g)x_i(k)$, and sending $[u]$ to $[\bar u]$ with $\bar u_i$ the matrix $u_i$ with rows and columns reindexed along $e^{G_i}$: $(\bar u_i)_{e(g',k'),e(g,k)}=(u_i)_{(g',k'),(g,k)}$.

*Proof sketch.* Reindexing along a bijection preserves identity matrices, products, transposes and $\mathbb Q$-linear combinations, and it keeps every entry beside the same pair of labels, so $\operatorname{prop}(\bar u_i)=\operatorname{prop}(u_i)$.

**Remark (not formalized).** [Forgetting the group on the free categories](../../signatures/point-functors/forget-functor.md) uses the same $e^G_n$, so that forgetting labels commutes strictly with forgetting the group.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)
