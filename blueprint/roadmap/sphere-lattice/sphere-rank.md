---
article_id: af_8f078b3a41876bb9cb8aef43
declaration: theorem
origin: cited
---

# Rational sphere calculation

For either $G_r = F_r$ or $G_r = E_r$, and $j \geq 0$,
$G_r(S^j) \otimes \Q \simeq (G_r(\pt) \otimes \Q) \oplus
(G_{r-j}(\pt) \otimes \Q)$. In particular, for odd $d$ both
$F_d(S^d) \otimes \Q$ and $E_d(S^d) \otimes \Q$ are
one-dimensional rational vector spaces.

*Proof sketch.* Split off the point summand. Localization
identifies the relative group of the pole cover with the reduced
group, and the other localization sequence identifies its boundary
as an isomorphism; the dense map between the two relative groups
is a rational isomorphism, giving
$\widetilde G_r(S^j) \otimes \Q \simeq
\widetilde G_{r-1}(S^{j-1}) \otimes \Q$. At $(r,j) = (d,d)$ the
summands are $0$ and $\Q$ by the point calculation.

## Sources

- [Preprint source map: `prop:sphere-rank`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)

## Proof depends on

- [Point groups](point-groups.md)
- [Witt localization](../localization/witt-localization.md)
- [Open cover dense inclusion](../localization/open-cover.md)
- [Dense doubling](../localization/dense-doubling.md)
- [Homotopy invariance](../sheaf-categories/homotopy-invariance.md)
