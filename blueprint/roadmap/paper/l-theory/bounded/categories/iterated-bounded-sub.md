---
article_id: af_8bbd1712ae0f78498b5c0883
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.subPow
---

# Iterated bounded subcategories

For a full subcategory $\mathcal U\subset\mathcal A$, the *iterated bounded subcategory* $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$ of the [iterated bounded category](iterated-bounded-category.md) is $\mathcal U$ for $j=0$ and, for $j\ge1$, $C_\mathbb Z$ of the previous level: the objects of $C_\mathbb Z(C_{\mathbb Z^{j-1}}\mathcal A)$ all of whose entries lie in $C_{\mathbb Z^{j-1}}\mathcal U$. If $\mathcal U$ is a full additive subcategory closed under duality, so is every $C_{\mathbb Z^j}\mathcal U$, by induction on $j$ with [bounded Karoubi filtrations](bounded-karoubi-filtration.md).

## Sources

- New: the $j$-fold iterate of $C_\mathbb Z\mathcal U$.

## Depends on

- [Iterated bounded categories](iterated-bounded-category.md), [bounded Karoubi filtrations](bounded-karoubi-filtration.md)
