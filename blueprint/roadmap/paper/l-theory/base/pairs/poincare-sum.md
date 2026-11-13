---
article_id: af_9d02361153dc9e64d436f15c
declaration: def
origin: background
statement: formalized
lean: HSP.SymPoincare.sum
---

# The sum of two Poincaré complexes

For strict $k$-dimensional symmetric Poincaré complexes $(C,\phi)$ and $(C',\phi')$ in a duality category $\mathcal B$, their *sum* $(C,\phi)\oplus(C',\phi')$ is the strict $k$-dimensional symmetric Poincaré complex $(C\oplus C',\phi\oplus\phi')$ of [Sums of Poincaré complexes](sum-of-poincare.md), where $\phi\oplus\phi'$ is the sum of [Sum of structured complexes](../complexes/sum-of-complexes.md). Equivalently, there is an isomorphism $u:C\oplus C'\to C''$ onto the chain complex $C''$ of the sum with $u_\%(\phi\oplus\phi')$ equal to its structure.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [A duality category has binary direct sums](../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../complexes/structure-complex.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Sums of Poincaré complexes](sum-of-poincare.md)
- [Pushforward preserves identities](../complexes/functors/push-id.md)
- [Pushforward of structures](../complexes/structure-push.md)
