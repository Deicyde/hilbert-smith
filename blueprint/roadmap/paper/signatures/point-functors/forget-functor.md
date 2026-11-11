---
article_id: af_1aa51bd59cfe5a4ff2b83857
declaration: def
origin: bridged
---

# Forgetting the group

Let $e^G_n:G\times\{1..n\}\to\{1..|G|n\}$, $e^G_n(g,k)=\varepsilon_G(g)\,n+k$, be the group enumeration of [forgetting the group](../../categories/functors/forget-group.md) on the asymptotic category. The strict duality functor $U_G:\mathrm{Free}(\mathbb Q[G])\to\mathrm{Free}(\mathbb Q)$ sends $n$ to $|G|n$ and a morphism $u:n\to n'$ to the matrix $\bar u$ with $\bar u_{e^G_{n'}(g',k'),e^G_n(g,k)}=u_{(g',k'),(g,k)}$.

*Proof sketch.* This is [reindexing](../../categories/asymptotic/free-set-basis.md) for the trivial group, whose orbit representatives are all basis elements, enumerated by $e^G$. It preserves identities, products and transposes. It is the same reindexing as in forgetting the group on $\mathcal A_{\mathbf G}(X)$, coordinate by coordinate.

## Sources

- HS paper, Section 3
- New: in the matrix model the coefficient-of-identity trace is built in, so forgetting is a reindexing of the same matrix.

## Depends on

- [Forgetting the group on the asymptotic category](../../categories/functors/forget-group.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
