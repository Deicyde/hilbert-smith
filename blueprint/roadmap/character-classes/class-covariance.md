---
article_id: af_ff88a81eddc1969447407608
declaration: theorem
origin: cited
---

# Covariance of character classes

Let $t : Y \to X$ be a compact test and $g : X \to X'$ a
continuous map of compact tests, with contractible neighborhood
bases at $b_t$ and $g(b_t)$. For every fixed finite partition of
$\Lambda$, $g_*z_i(t) = z_i(gt)$ in $E_d(X')$.

*Proof sketch.* Pushforward gives a duality-preserving quotient
functor commuting with the localization isomorphisms, carrying the
total form to $(A_{gt},\alpha_{gt})$. Representing a projector by a
roof and pushing through the neighborhood
$N' = X' \setminus g(X \setminus N)$ computes it entirely where it
agrees with its character description; open base change identifies
this with the projector for $gt$, and the germ theorem gives
equality in the quotient.

## Sources

- [Preprint source map: `prop:class-covariance`](../../sources/preprint.md)

## Depends on

- [Character classes](character-classes.md)

## Proof depends on

- [Character coproducts](character-coproduct.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
- [Witt localization](../localization/witt-localization.md)
- [Germ description](../localization/germs.md)
