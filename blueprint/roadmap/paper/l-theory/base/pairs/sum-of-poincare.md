---
article_id: af_5388ecd14d2f776f737a9a44
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPoincare.exists_sum
proof: formalized
---

# Sums of Poincaré complexes

If $(C,\phi)$ and $(C',\phi')$ are strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$, then so is $(C\oplus C',\phi\oplus\phi')$, with the sum of [Sum of structured complexes](../complexes/sum-of-complexes.md).

*Proof sketch.* (1) $\phi\oplus\phi'=i_\%\phi+i'_\%\phi'$ is a cycle and $T$-invariant, since pushforward commutes with $\partial$ and with $T$; a sum of zero objects is a zero object. (2) $(\phi\oplus\phi')_\natural=\phi_\natural\oplus\phi'_\natural$ up to the canonical isomorphism $(C\oplus C')^{k-*}\cong C^{k-*}\oplus C'^{k-*}$, so it is an equivalence: a sum of chain homotopy equivalences is one, with the sum of the inverses and of the homotopies.

## Sources

- [Ranicki 1980 I, §1](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the boundary step of [Sums of pairs](sum-of-pairs.md), for complexes

## Depends on

- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../complexes/structure-complex.md)

## Proof depends on

- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Dual complex](../complexes/dual-complex.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Duals of chain maps reverse composition](../complexes/functors/dual-map-comp.md)
- [Duals of identity chain maps](../complexes/functors/dual-map-id.md)
- [Pushforward commutes with the boundary](../complexes/functors/push-boundary.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual of a chain map](../complexes/functors/dual-map.md)
- [The involution T](../complexes/structure-involution.md)
