---
article_id: af_7ed2bf550791ea828015df4a
declaration: lemma
origin: background
---

# Idempotent completion of the free category

For a finite group $G$, $\mathrm{Kar}\,\mathrm{Free}(G)$, for the [free category](../../categories/asymptotic/free-category.md) $\mathrm{Free}(G)$, is $\mathbb Q$-linearly equivalent to the category of finitely generated $\mathbb Q[G]$-modules. Every such module is semisimple of finite length.

*Proof sketch.* (1) $\mathrm{Free}(G)$ is the category of based free $\mathbb Q[G]$-modules: sending an equivariant matrix $a:n\to m$ to the $m\times n$ matrix over $\mathbb Q[G]$ with entries $\sum_{x\in G}a_{(1,k),(x,l)}\,x$ is bijective on morphisms and compatible with composition, and it carries the transpose to the transpose followed by $g\mapsto g^{-1}$ on entries. (2) $(M,e)\mapsto\mathrm{im}\,e$ is fully faithful onto the finitely generated projectives. (3) By Maschke, every finitely generated module is projective and semisimple.

**Remark (not formalized).** Step (1) is why the group-ring model of the point categories, based free $\mathbb Q[G_i]$-modules with the transpose and $g\mapsto g^{-1}$, is the same duality category as $\mathrm{Free}(G_i)$.

## Sources

- Maschke; [Weibel 2013, II](../../../../sources/paper/weibel-2013.md) [U]

## Depends on

- [Free category](../../categories/asymptotic/free-category.md)
- [Idempotent completion with duality](../base/categories/karoubi-duality.md)
