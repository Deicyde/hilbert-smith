---
article_id: af_dbd5b9a95dd63495bb708783
declaration: theorem
origin: cited
---

# Contradiction on the invariant chart

For every $n \geq 1$ and every prime $p$, an
orientation-preserving continuous $\Zp$-action on a connected open
subset of $\R^n$ has nonzero kernel.

*Proof sketch.* Suppose the action faithful. Fix the lattice $L_d$
first, then choose $k$ with $m = p^k > 4L_d$ and the cyclic
partition. Moving the test gives $h \simeq D_sa$ constant off the
sheet region; equal parts, homotopy, covariance, and the degree
action give $D_{s*}z_i(a) = D_{s*}z_j(a)$, and cancelling the
nonzero rational scalar $s$ equates all $\bar z_i(a)$ while the
classes stay integral in the fixed lattice. The coefficient form is
two positive real lines, so $[A_a,\alpha_a]$ has rational image
$2\bar u_d$ and the sum formula gives each
$\bar z_i(a) = (4/m)\bar u_d$, forcing $4L_d/m \in \Z$ with
$0 < 4L_d/m < 1$: contradiction.

## Sources

- [Preprint source map: `thm:contradiction`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fixed sphere lattice](../sphere-lattice/sphere-lattice.md)
- [Collapse and compactification](../local-tests/collapse.md)
- [Averaged degree-one test](../local-tests/averaged-test.md)
- [Finite quotient sheets](../local-tests/finite-sheets.md)
- [Moving a test](../local-tests/move-test.md)
- [Equal parts](equal-parts.md)
- [Homotopy of character classes](class-homotopy.md)
- [Covariance of character classes](class-covariance.md)
- [Action of degree](../sphere-lattice/degree-action.md)
- [Sum of the character classes](sum-classes.md)
