---
article_id: af_ed8b36af2b0fca1369826cce
declaration: def
origin: bridged
statement: formalized
lean: HSP.supp
---

# Support subcategory

For any $S\subseteq X$ (in every use $S$ is closed and invariant; the definition needs neither), $\mathcal A_S$ is the full subcategory of $\mathcal A_{\mathbf G}(X)$ on the objects such that for every $\varepsilon>0$, eventually all $x_i(k)$ lie in the open $\varepsilon$-thickening of $S$. It contains the empty object, the concatenation of any two of its objects, and $M^*=M$ with $M$, so it is a [full additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md).

**Remark (not formalized).** $\mathcal A_\varnothing$ consists of the objects that have no generators at level $i$ for all but finitely many $i$, and $\mathcal A_X$ consists of all objects.

## Sources

- HS paper, Section 2

## Depends on

- [Additive subcategory closed under duality](../../l-theory/base/categories/dual-additive-subcategory.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
