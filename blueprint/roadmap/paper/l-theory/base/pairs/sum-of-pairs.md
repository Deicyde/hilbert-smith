---
article_id: af_7f7823629e69706a800e80d7
declaration: lemma
origin: bridged
---

# Sums of pairs

If $(f:C\to D,\delta\phi,\phi)$ and $(f':C'\to D',\delta\phi',\phi')$ are strict $n$-dimensional Poincaré pairs in $\mathrm{Kar}\,\mathcal A$, then so is $(f\oplus f':C\oplus C'\to D\oplus D',\ \delta\phi\oplus\delta\phi',\ \phi\oplus\phi')$, with the sums of [Sum of structured complexes](../complexes/sum-of-complexes.md).

*Proof sketch.* (1) Cycle, $T$-invariance, the identity $\partial(\delta\phi\oplus\delta\phi')=(f\oplus f')_\%(\phi\oplus\phi')$ and the support conditions hold componentwise; a sum of zero objects is a zero object. (2) $(\phi\oplus\phi')_\natural=\phi_\natural\oplus\phi'_\natural$ up to the canonical isomorphism $(C\oplus C')^{n-1-*}\cong C^{n-1-*}\oplus C'^{n-1-*}$, so the boundary is Poincaré by [Sums of equivalences](../complexes/sum-equivalence.md). (3) $\mathcal C(f\oplus f')=\mathcal C(f)\oplus\mathcal C(f')$, and under the canonical isomorphism $(D\oplus D')^{n-*}\cong D^{n-*}\oplus D'^{n-*}$ the pair map of the sum is $\psi\oplus\psi'$. It is an equivalence by [Sums of equivalences](../complexes/sum-equivalence.md).

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)

## Proof depends on

- [Sums of equivalences](../complexes/sum-equivalence.md)
