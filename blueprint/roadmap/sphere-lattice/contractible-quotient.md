---
article_id: af_0a8a6e9d29bab02bfd6951b2
declaration: theorem
origin: cited
---

# Contractible quotient

Let $d \geq 3$ be odd, $X$ any test space for $\T$, and
$U \subset X$ a nonempty contractible open subset. The quotient
functor induces an integral isomorphism
$E_d(X) \xrightarrow{\sim} W_d(\T(X)/\T(U))$, natural for
continuous $g : X \to X'$ with $g(U) \subset U'$ for contractible
$U'$.

*Proof sketch.* Homotopy invariance plus the point calculation
gives $E_d(U) = 0$, and $E_{d-1}(U) \to E_{d-1}(X)$ is split
injective via projection to the point (in both odd congruence
classes of $d$ mod 4). The localization sequence then collapses to
the asserted integral isomorphism; no rationalization or splitting
of quotient idempotents is involved. Naturality follows from the
natural localization sequence since $g_*$ preserves support
subcategories.

## Sources

- [Preprint source map: `prop:contractible-quotient`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)

## Proof depends on

- [Homotopy invariance](../sheaf-categories/homotopy-invariance.md)
- [Point groups](point-groups.md)
- [Witt localization](../localization/witt-localization.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
