---
article_id: af_dc5c41e29e895bd48c529982
declaration: lemma
origin: cited
---

# Cutoff

Let $K \subset O \subset X$ with $K$ closed and $O$ open. For every
$A \in \Bzero(X)$ there is a morphism $s : A' \to A$ such that $A'$
is extended from $\Bzero(O)$, its cohomology vanishes outside a
compact subset of $O$, and $s$ restricts to an isomorphism on some
open neighborhood of $K$.

*Proof sketch.* For a simplex generator, subdivide so the closed
stars of simplices meeting $f^{-1}K$ lie in $f^{-1}O$; a
vertex-valued function gives a polyhedral neighborhood $E$ with
polyhedral closure inside $f^{-1}O$, and the extension-by-zero map
is an isomorphism over $X \setminus f(\Delta \setminus E)$. Shifts
and sums are immediate; cones are cut off compatibly by lifting
through open-extension adjunction over the intersection of the two
invertibility neighborhoods.

## Sources

- [Preprint source map: `lem:cutoff`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)

## Proof depends on

- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
