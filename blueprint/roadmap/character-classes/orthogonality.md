---
article_id: af_def62825035d9e43170364d3
declaration: lemma
origin: cited
---

# Real orthogonality

If $D, E \subset \Lambda$ are disjoint, the cross pairing between
$B_D$ and $B_E$ induced by the restricted test form is zero. In
particular, the projectors of any finite partition of $\Lambda$
are self-adjoint.

*Proof sketch.* The orientation-preserving $G$-action acts by
isometries, with $T^\dagger = T^{-1}$ and
$M_\lambda^\dagger = M_{\lambda^{-1}}$. For $\lambda \notin E$,
$T - M_\lambda$ vanishes on $B_{\{\lambda\}}$ while
$T^{-1} - M_{\lambda^{-1}}$ is invertible on $B_E$ (componentwise
inverses $(\mu^{-1}-\lambda^{-1})^{-1}$); adjointness kills the
cross pairing. Coproduct universality extends this from singletons
to arbitrary disjoint $D, E$, including conjugate pairs.

## Sources

- [Preprint source map: `lem:orthogonality`](../../sources/preprint.md)

## Depends on

- [Character coproducts](character-coproduct.md)

## Proof depends on

- [Character coproducts](character-coproduct.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
