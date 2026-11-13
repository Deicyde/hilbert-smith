---
article_id: af_7f7823629e69706a800e80d7
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPair.sum
proof: formalized
---

# Sums of pairs

If $(f:C\to D,\delta\phi,\phi)$ and $(f':C'\to D',\delta\phi',\phi')$ are strict $n$-dimensional Poincaré pairs in a duality category $\mathcal B$, then so is $(f\oplus f':C\oplus C'\to D\oplus D',\ \delta\phi\oplus\delta\phi',\ \phi\oplus\phi')$, with the sums of [Sum of structured complexes](../complexes/sum-of-complexes.md).

*Proof sketch.* (1) Cycle, $T$-invariance, the identity $\partial(\delta\phi\oplus\delta\phi')=(f\oplus f')_\%(\phi\oplus\phi')$ and the support conditions hold componentwise; a sum of zero objects is a zero object. (2) The boundary $(C\oplus C',\phi\oplus\phi')$ is Poincaré by [Sums of Poincaré complexes](sum-of-poincare.md). (3) The maps of cones induced by the biproduct projections and inclusions give an isomorphism $\mathcal C(f\oplus f')\cong\mathcal C(f)\oplus\mathcal C(f')$. Under it and the canonical isomorphism $(D\oplus D')^{n-*}\cong D^{n-*}\oplus D'^{n-*}$, the pair map of the sum is $\psi\oplus\psi'$. This is an equivalence: take the sums of the inverses and of the homotopies.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../complexes/structure-complex.md)

## Proof depends on

- [Sums of Poincaré complexes](sum-of-poincare.md)
- [Duals of chain maps reverse composition](../complexes/functors/dual-map-comp.md)
- [Duals of identity chain maps](../complexes/functors/dual-map-id.md)
- [Pushforward preserves composition](../complexes/functors/push-comp.md)
- [Pushforward commutes with the boundary](../complexes/functors/push-boundary.md)
- [Mapping cone](../complexes/cone.md)
- [Duality map of a cycle](../complexes/cycle-chain-map.md)
- [Dual complex](../complexes/dual-complex.md)
- [Dual of a chain map](../complexes/functors/dual-map.md)
- [The involution T](../complexes/structure-involution.md)
- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Pair map](pair-map.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
