---
article_id: af_299f24b409ae090119e3e3f3
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cls_eq_zero_of_isEmpty
proof: formalized
---

# The class over an empty space vanishes

Let $X$ be an empty metric space with a $C_p$-action, $\mathbf G$ a group sequence and $Z\subseteq X$. Every strict $k$-dimensional symmetric Poincaré complex $(C,\phi)$ in the [exterior quotient](../categories/supports/exterior-quotient.md) $\mathcal B_{\mathbf G,Z}(X)$ has $\operatorname{cls}(C,\phi)=0$, where $\operatorname{cls}$ is the [class map](../l-theory/ultimate/groups/ultimate-cls.md) of the complex read in $\operatorname{Kar}\mathcal B_{\mathbf G,Z}(X)$ through the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md), its image under the induced functor of [duality functors on Poincaré complexes](../l-theory/base/pairs/functor-poincare.md).

*Proof sketch.* An object $(n_i,x_i)$ of the [asymptotic category](../categories/asymptotic/asymptotic-category.md) over $X$ has labels $x_i:\{1..n_i\}\to X$, so $n_i=0$ for every $i$; its identity is then the empty matrix at every level, so it is a zero object. Zero objects stay zero under the quotient functor and the Karoubi embedding, so every chain object of the image of $C$ is zero. The map to the [zero Poincaré complex](../l-theory/base/pairs/poincare-zero.md) is an isomorphism of complexes, and every structure on the zero complex vanishes, so [homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md) (with $\chi=0$) gives $[C,\phi]=0$ in the [L-group](../l-theory/base/groups/l-group.md), and $\operatorname{cls}$ is additive.

## Sources

- New: the case of an empty control space in the proof of local exclusion.

## Depends on

- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)
- [L-group](../l-theory/base/groups/l-group.md)

## Proof depends on

- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Free category of a finite group](../categories/asymptotic/free-category.md)
- [Zero Poincaré complex](../l-theory/base/pairs/poincare-zero.md)
- [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md)
- [Group structure on L](../l-theory/base/groups/l-group-add.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
