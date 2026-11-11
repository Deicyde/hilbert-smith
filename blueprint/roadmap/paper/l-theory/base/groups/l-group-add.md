---
article_id: af_a376b5aa3925993024cfc900
declaration: instance
origin: bridged
statement: formalized
lean: HSP.LGroup.instAddCommGroup
---

# Group structure on L

For a duality category $\mathcal B$, $L_k(\mathcal B)$ is an abelian group with $[C,\phi]+[C',\phi']=[C\oplus C',\phi\oplus\phi']$, zero $[0,0]$ and negation $-[C,\phi]=[C,-\phi]$.

Here $(C,\phi)\oplus(C',\phi')$, $(C,-\phi)$ and $(0,0)$ are the strict Poincaré complexes of [Sums of Poincaré complexes](../pairs/sum-of-poincare.md).

*Proof sketch.* The operations are well defined on cobordism classes, and satisfy associativity, commutativity, the unit law and the inverse law, by [Sum of Poincaré complexes up to cobordism](l-group-add-laws.md).

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [L-group](l-group.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Sums of Poincaré complexes](../pairs/sum-of-poincare.md)

## Proof depends on

- [Sum of Poincaré complexes up to cobordism](l-group-add-laws.md)
