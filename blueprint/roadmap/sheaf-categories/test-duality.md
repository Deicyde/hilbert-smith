---
article_id: af_c3e7c8bcc43e08ec0beb7166
declaration: theorem
origin: cited
---

# Verdier duality on test categories

The Verdier operation $\D_X A = R\mathcal Hom(A, \omega_X)$
restricts to a triangulated duality on each of $\Tzero(X)$,
$\T(X)$, $\Pzero(X)$, and $\Pcat(X)$. For every object $A$ in one of
these categories, $\D_X A$ belongs to the same category and the
canonical biduality map $A \to \D_X^2 A$ is an isomorphism. There is
a compact $K \subset X$ outside which both $A$ and $\D_X A$ vanish.

*Proof sketch.* On a closed $n$-simplex, a half-ball local
calculation gives $\D_\Delta\underline\R_\Delta \simeq
j_!\underline\R_{\Delta^\circ}[n]$ and biduality is the unit
isomorphism, including at the boundary. For a simplex generator
$Rf_*\underline\R_\Delta$, properness plus the internal duality
formula gives $\D_X A \simeq Rf_*\omega_\Delta$, which lies in the
same category by the boundary triangle; a tensor--Hom diagram shows
proper duality transports the canonical biduality map. The duality
class is closed under shifts, triangles, and summands. Compact
support passes to duals by open restriction of duality.

## Sources

- [Preprint source map: `prop:test-duality`](../../sources/preprint.md)

## Depends on

- [Test categories](test-categories.md)

## Proof depends on

- [Simplex generators](simplex-generators.md)
- [Verdier duality formalism](../background/verdier-duality.md)
- [Sheaf pushforward toolkit](../background/sheaf-pushforward.md)
