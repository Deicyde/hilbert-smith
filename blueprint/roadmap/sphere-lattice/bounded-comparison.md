---
article_id: af_859412908101fc84311a673d
declaration: theorem
origin: cited
---

# Bounded comparison

For every $j \geq 0$ there is a nonnegative integer $e_j$,
independent of $r$, such that the kernel and cokernel of
$F_r(S^j) \to E_r(S^j)$ are annihilated by $2^{e_j}$ for every
integer $r$.

*Proof sketch.* Induction on $j$ with $e_0 = 0$. For the pole cover
$X = U \cup V$ with $I = U \cap V \simeq S^{j-1}$, homotopy
invariance makes the comparisons on $U, V$ isomorphisms and bounds
those on $I$. A five-term chase through the localization rows
bounds the comparison on relative groups; the square chase with the
exponent-two dense maps transfers it across the cover; a final
five-term chase bounds the middle comparison. The exponents compose
as $e \mapsto 3e \mapsto 3e+2 \mapsto 9e+6$, so one may take
$e_j = 3(9^j-1)/4$, but only existence is used.

## Sources

- [Preprint source map: `thm:bounded-comparison`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)

## Proof depends on

- [Point groups](point-groups.md)
- [Homotopy invariance](../sheaf-categories/homotopy-invariance.md)
- [Witt localization](../localization/witt-localization.md)
- [Open cover dense inclusion](../localization/open-cover.md)
- [Dense doubling](../localization/dense-doubling.md)
- [Finite diagram chases](finite-chases.md)
