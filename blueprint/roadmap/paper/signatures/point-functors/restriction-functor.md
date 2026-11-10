---
article_id: af_db70bc1eedb232d11ab79014
declaration: def
origin: background
---

# Restriction to a subgroup

Let $H\le G$ and fix representatives $g_1,\dots,g_m$ of the right cosets, $G=\bigsqcup_jHg_j$, $m=[G:H]$, and an enumeration of $\{1..m\}\times\{1..n\}$ by $\{1..mn\}$. The strict duality functor $\mathrm{res}^G_H:\mathrm{Free}(\mathbb Q[G])\to\mathrm{Free}(\mathbb Q[H])$ sends $n$ to $mn$ and a morphism $u:n\to n'$ to its reindexing, by [bases of finite free sets](../../categories/asymptotic/free-set-basis.md), as an $H$-equivariant matrix on the $H$-sets $G\times\{1..n\}$ and $G\times\{1..n'\}$ (action $h(g,k)=(hg,k)$) with the orbit representatives $(g_j,k)$ and $(g_j,k')$. Explicitly, $\mathrm{res}^G_H(u)_{(h',(j',k')),(h,(j,k))}=u_{(h'g_{j'},k'),(hg_j,k)}$.

*Proof sketch.* The $H$-action on $G\times\{1..n\}$ is free, and every orbit contains exactly one $(g_j,k)$, because $Hg\ni g_j$ for exactly one $j$. A $G$-equivariant matrix is $H$-equivariant. [Reindexing](../../categories/asymptotic/free-set-basis.md) preserves identities, products and transposes, so $\mathrm{res}^G_H$ is a functor that commutes strictly with transposition.

## Sources

- [published: restriction of representations] [U]
- New: the restriction is written in the standard-basis model of the free category by reindexing.

## Depends on

- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Bases of finite free G-sets](../../categories/asymptotic/free-set-basis.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
