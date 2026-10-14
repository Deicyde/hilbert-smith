---
article_id: af_ecced78b76146b7df0b1a4b6
declaration: theorem
origin: cited
---

# Homotopy of character classes

For a fixed partition of $\Lambda$, homotopic maps
$t_0, t_1 : Y \to S^d$ satisfy $z_i(t_0) = z_i(t_1)$ in
$E_d(S^d)$.

*Proof sketch.* Uniform continuity subdivides the homotopy into
close stages landing in the compact semialgebraic test
$C_d = \{(x_0,x_1) : \langle x_0,x_1\rangle \geq 0\}$, a smooth
$2d$-manifold with boundary having contractible neighborhood bases
everywhere. Its two projections are homotopic via normalized
interpolation, so covariance plus homotopy invariance equates the
classes at consecutive stages; iteration gives the result.

## Sources

- [Preprint source map: `prop:class-homotopy`](../../sources/preprint.md)

## Depends on

- [Character classes](character-classes.md)

## Proof depends on

- [Covariance of character classes](class-covariance.md)
- [Homotopy invariance](../sheaf-categories/homotopy-invariance.md)
