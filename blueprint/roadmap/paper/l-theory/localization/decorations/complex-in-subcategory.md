---
article_id: af_81fd7cd3ed500a8232583392
declaration: def
origin: background
statement: formalized
lean: HSP.SymPoincare.toSub
---

# Complexes in a full subcategory

Let $\mathcal B$ be a [duality category](../../base/categories/duality-category.md) and $\mathcal P\subset\mathcal B$ a [full additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md), itself a duality category with the [restricted duality](../../base/categories/dual-subcategory.md). If every chain object of a [strict $k$-dimensional symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md) $(C,\phi)$ in $\mathcal B$ lies in $\mathcal P$, then the same chain objects, differentials and structure form a strict $k$-dimensional symmetric Poincaré complex in $\mathcal P$, whose image under the inclusion $\mathcal P\to\mathcal B$ is $(C,\phi)$.

*Proof sketch.* The inclusion is a strict duality functor and fully faithful. The conditions $\partial\phi=0$ and $T\phi=\phi$ hold in $\mathcal P$ because the inclusion is faithful and commutes with $\partial$ and $T$ ([Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)). A chain homotopy equivalence $\phi_\natural:C^{k-*}\to C$ in $\mathcal B$ between complexes with chain objects in $\mathcal P$ is one in $\mathcal P$: its inverse and both homotopies have components between objects of $\mathcal P$, so they lift, and the chain map and homotopy identities lift because the inclusion is faithful.

## Sources

- New: the restriction of a complex to a full subcategory containing its chain objects.

## Depends on

- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)

## Proof depends on

- [Duality functors carry Poincaré complexes](../../base/pairs/functor-poincare.md)
