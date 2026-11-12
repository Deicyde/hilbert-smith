---
article_id: af_72e3d8e3e2fbce9cc18c9eec
declaration: instance
origin: bridged
statement: formalized
lean: HSP.PCat.dualCat, HSP.PCat
---

# Sequence category

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](group-sequence.md). The duality category $\mathcal P_{\mathbf G}=\prod_i\mathrm{Free}(\mathbb Q[G_i])$ has as objects the sequences $(n_i)$ of objects of [$\mathrm{Free}(\mathbb Q[G_i])$](free-category.md) and as morphisms the sequences $(u_i)$ of morphisms, with composition, identities, sums and the duality $(n_i)^*=(n_i)$, $(u_i)^*=(u_i^{T})$ taken coordinatewise. Only the groups $G_i$ enter, not the $\chi_i$.

## Sources

- HS paper, Section 3

## Depends on

- [Free category of a finite group](free-category.md)
- [Group sequence](group-sequence.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)
- [Objects of rank zero are zero](free-zero.md)
