---
article_id: af_5388ecd14d2f776f737a9a44
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.SymPoincare.exists_sum
---

# Sums of Poincaré complexes

If $(C,\phi)$ and $(C',\phi')$ are strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$, then so is $(C\oplus C',\phi\oplus\phi')$, with the sum of [Sum of structured complexes](../complexes/sum-of-complexes.md); write $(C,\phi)\oplus(C',\phi')$ for it. Likewise $(C,-\phi)$ and the zero complex with the zero structure, $(0,0)$, are strict $k$-dimensional symmetric Poincaré complexes. The negative and the zero complex are constructions; the statement proper is the sum.

*Proof sketch.* (1) $\phi\oplus\phi'=i_\%\phi+i'_\%\phi'$ is a cycle and $T$-invariant, since pushforward commutes with $\partial$ and with $T$; a sum of zero objects is a zero object. (2) $(\phi\oplus\phi')_\natural=\phi_\natural\oplus\phi'_\natural$ up to the canonical isomorphism $(C\oplus C')^{k-*}\cong C^{k-*}\oplus C'^{k-*}$, so it is an equivalence by [Sums of equivalences](../complexes/sum-equivalence.md). (3) $(-\phi)_\natural=-\phi_\natural$, and negating an equivalence, its inverse and its homotopies gives an equivalence. (4) For $(0,0)$ all chain objects of $0$ and $0^{k-*}$ are zero objects, so $0_\natural$ is an isomorphism.

## Sources

- [Ranicki 1980 I, §1](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the boundary step of [Sums of pairs](sum-of-pairs.md), for complexes

## Depends on

- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)

## Proof depends on

- [Pushforward commutes with T](../complexes/structure-push-involution.md)
- [Sums of equivalences](../complexes/sum-equivalence.md)
