---
article_id: af_4a2f7da8448eb69417b67e16
declaration: structure
origin: background
statement: formalized
lean: HSP.UPair
---

# U-pairs

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](../decorations/decorated-object.md). Here $\mathrm{Kar}\,\mathcal U$ is the idempotent completion of $\mathcal U$, with objects $(V,e)$ for $V\in\mathcal U$, and $i=\mathrm{Kar}(\mathrm{incl}):\mathrm{Kar}\,\mathcal U\to\mathrm{Kar}\,\mathcal A$ is the [completion](../../base/categories/karoubi-functor.md) of the inclusion, a strict duality functor. So $L^p_k(\mathcal U)=L_k(\mathrm{Kar}\,\mathcal U)$. A *strict $k$-dimensional $\mathcal U$-pair* $V$ over $(P,\pi)$ consists of
- a strict $(k-1)$-dimensional symmetric Poincaré complex $(P,\pi)$ in $\mathrm{Kar}\,\mathcal U$, and
- a strict $k$-dimensional Poincaré pair $(f:iP\to D,\delta\phi,i_\%\pi)$ in $\mathrm{Kar}\,\mathcal A$.

**Remark (not formalized).** $i$ is fully faithful, and its essential image is the full subcategory $\mathrm{Kar}\,\mathcal U\subset\mathrm{Kar}\,\mathcal A$ of [Completion of a subcategory](../../base/categories/kar-subcategory.md) (its Remark (a)). The proofs work with either meaning; this paper uses the completion of $\mathcal U$ throughout.

## Sources

- New: the data of a relative cycle for $\mathcal U\subset\mathcal A$, as in the HS paper, Section 6

## Depends on

- [Decorated objects](../decorations/decorated-object.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
