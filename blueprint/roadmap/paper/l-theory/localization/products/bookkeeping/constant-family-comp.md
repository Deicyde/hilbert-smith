---
article_id: af_d7ca1d9f745844de550865c4
declaration: lemma
origin: background
statement: formalized
lean: HSP.constFamily_comp_entry
proof: formalized
---

# Entries of composites of constant families

In $C_\mathbb Z(\mathbb Q)$, for the category $\mathbb Q$ of [based vector spaces](based-category.md), let $f:M\to N$ and $g:N\to P$ be maps whose components $f_{mn}$ and $g_{lm}$ are matrices with all entries equal to $c(m,n)$ and $c'(l,m)$ respectively, where $c(m,n)=0$ for $|m-n|>1$. Then every entry of the component $(gf)_{ln}$ is
$$\sum_{m=n-1}^{n+1}d_m\,c'(l,m)\,c(m,n),$$
where $\mathbb Q^{d_m}$ is the object of $N$ in position $m$.

*Proof sketch.* $(gf)_{ln}=\sum_mg_{lm}f_{mn}$, where only $m\in[n-1,n+1]$ contribute because $f_{mn}=0$ otherwise. An entry of the product of a constant $a\times d_m$ matrix with value $c'(l,m)$ and a constant $d_m\times b$ matrix with value $c(m,n)$ is $d_m\,c'(l,m)\,c(m,n)$.

## Sources

- New: bookkeeping for the explicit maps of the symmetric line.

## Depends on

- [The category of based ℚ-vector spaces](based-category.md)
- [The bounded category](../../../bounded/categories/bounded-category.md)
