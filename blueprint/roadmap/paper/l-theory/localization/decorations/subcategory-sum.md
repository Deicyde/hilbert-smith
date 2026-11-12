---
article_id: af_8fb404dcc8c8ff08b8a1cbbc
declaration: lemma
origin: background
statement: formalized
lean: HSP.SymPoincare.mk_eq_add_of_sumIso
proof: formalized
---

# Sums in a full subcategory

Let $\mathcal P\subset\mathcal B$ be a full additive subcategory of a duality category, closed under duality, and let $(Z,\zeta)$, $(C,\phi)$, $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in $\mathcal P$ ([Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)). If an isomorphism of complexes $Z\cong C\oplus C'$ in $\mathcal B$ carries $\zeta$ to $\phi\oplus\phi'$, then
$$[Z,\zeta]=[C,\phi]+[C',\phi']\quad\text{in }L_k(\mathcal P).$$

In particular this applies to [complexes in $\mathcal P$](complex-in-subcategory.md) given by complexes in $\mathcal B$ all of whose chain objects lie in $\mathcal P$.

*Proof sketch.* The inclusion of $\mathcal P$ preserves sums, so $C\oplus C'$ is isomorphic to the image of the sum of $C$ and $C'$ in $\mathcal P$, compatibly with the inclusions of the summands. The composite isomorphism lifts to $\mathcal P$ because the inclusion is fully faithful, and it carries $\zeta$ to $\phi\oplus\phi'$ there, as one checks after the inclusion ([Duality functors commute with pushforward](../../base/complexes/functor-push.md)). [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md) with $\chi=0$ and the [group structure on L](../../base/groups/l-group-add.md) give the claim.

## Sources

- New: bookkeeping for decorated L-groups.

## Depends on

- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Complexes in a full subcategory](complex-in-subcategory.md)
- [The sum of two Poincaré complexes](../../base/pairs/poincare-sum.md)
- [Sum of structured complexes](../../base/complexes/sum-of-complexes.md)
- [Group structure on L](../../base/groups/l-group-add.md)
- [Image of structures under a duality functor](../../base/complexes/functors/functor-structure.md)
- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)

## Proof depends on

- [Homotopy-isometry invariance](../../base/groups/homotopy-isometry-invariance.md)
- [Duality functors commute with pushforward](../../base/complexes/functor-push.md)
- [Pushforward preserves composition](../../base/complexes/functors/push-comp.md)
