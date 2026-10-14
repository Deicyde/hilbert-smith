---
article_id: af_68cf160423e4521a8ef0c338
declaration: theorem
origin: cited
---

# Direct images and open extension

For an allowed map $g : X \to Y$, direct image induces exact
functors $g_* : \Tzero(X) \to \Tzero(Y)$ and $g_* : \T(X) \to \T(Y)$,
and the analogues for $\Pzero, \Pcat$. They are given by
$Rg_! \simeq Rg_*$ on these categories, commute coherently with
Verdier duality and its shifts, and are compatible with
composition. For an open inclusion $j : U \hookrightarrow X$, this
functor is $j_!$ and is fully faithful.

*Proof sketch.* An object vanishing outside compact $K$ factors
through $K$, where $gi$ is proper, identifying $Rg_! \to Rg_*$ with
an invertible comparison. Generators map to generators by
composition. Compact support of both $A$ and $\D_X A$ gives the
duality comparison via evaluation, cup map, and trace; traces
compose. For open inclusions, $Rj_! = j_!$ and the adjunction
$(j_!, j^{-1})$ gives full faithfulness.

## Sources

- [Preprint source map: `prop:test-pushforward`](../../sources/preprint.md)

## Depends on

- [Test categories](test-categories.md)

## Proof depends on

- [Verdier duality on test categories](test-duality.md)
- [Verdier duality formalism](../background/verdier-duality.md)
- [Sheaf pushforward toolkit](../background/sheaf-pushforward.md)
