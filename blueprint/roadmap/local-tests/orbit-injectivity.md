---
article_id: af_980b69caddcd2057231424bb
declaration: lemma
origin: cited
---

# Rational orbit pullback

Let $E$ be compact metrizable with a continuous $G$-action and
$r : E \to E/G$ its orbit map. For any field $k$,
$Rr_*\underline k_E \simeq r_*\underline k_E$ in the bounded-below
derived category. For $k = \Q$ the unit
$\underline\Q_{E/G} \to r_*\underline\Q_E$ has a natural sheaf
retraction, so
$r^* : \check H^j(E/G;\Q) \to \check H^j(E;\Q)$ is injective for
every $j$.

*Proof sketch.* Each orbit is compact zero-dimensional, where
global sections of vector-space sheaves are exact, so higher fiber
cohomology vanishes and proper base change gives the first claim
with no dimension bound. A locally constant rational function on a
saturated preimage factors through a finite quotient, so Haar
averaging is rational; a finite-cover argument shows the average is
locally constant and descends, giving the sheaf retraction, and the
Cech--sheaf comparison transfers split injectivity.

## Sources

- [Preprint source map: `lem:orbit-injectivity`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Stacks derived facts](../background/stacks-derived.md)
- [Closed subgroups of $\Zp$](../background/padic-subgroups.md)
- [Cech comparison](../background/cech-comparison.md)
