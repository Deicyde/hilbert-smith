---
article_id: af_72d75e9bb517b9198f3926e0
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.LGroup.mk_eq_of_homotopyIsometry
proof: formalized
---

# Homotopy-isometry invariance

Let $(C,\phi)$ and $(C',\phi')$ be strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$, $h:C\to C'$ a chain homotopy equivalence, and $\chi\in M(C')_{k+1}$ with $\partial\chi=h_\%\phi-\phi'$. Then $[C,\phi]=[C',\phi']$ in $L_k(\mathcal B)$.

*Proof sketch.* [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md) with $\mathcal P$ all objects gives a cobordism; then use the definition of the [L-group](l-group.md).

## Sources

- [Ranicki 1989, Def 3.10](../../../../../sources/paper/ranicki-1989.md) [U]
- HS paper, Section 5

## Depends on

- [L-group](l-group.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Structure complex](../complexes/structure-complex.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Strict symmetric Poincaré complex](../pairs/symmetric-poincare-complex.md)

## Proof depends on

- [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md)
- [Cobordism](../pairs/cobordism.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [The involution T](../complexes/structure-involution.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Strict Poincaré pair](../pairs/poincare-pair.md)
