---
article_id: af_ae953417fe55e04c4cac64f9
declaration: lemma
origin: cited
lean: HilbertSmith.Interface.averagedTest HilbertSmith.Interface.aqc_homotopic_id HilbertSmith.Interface.LocalAction.pinch HilbertSmith.Interface.LocalAction.pinch_comp_c_homotopic
---

# Averaged degree-one test

After replacing $G$ by an open subgroup identified with $\Zp$,
with $q : W^+ \to Y = W^+/G$, there is a continuous map
$a : Y \to S^d$ with $\deg(aqc) = 1$. Moreover $aq$ is homotopic
on $W^+$ to a degree-one pinch supported in a round ball compactly
contained in $W$.

*Proof sketch.* A ball pinch $P_{z,r}$ has degree one after $c$.
For a small enough open subgroup, the pinch is uniformly close to
its Haar average $A$; normalizing the straight-line homotopy gives
an invariant sphere-valued map homotopic to the pinch, fixing
$\infty$ and constant outside a compact subset of $W$. It descends
to $a$, and faithfulness plus orientation preservation persist.

*Formalization.* `averagedTest` proves the pinch form: $aq$ is
homotopic on $W^+$ to a pinch $P_{z,r}$ (`LocalAction.pinch`, with
$P = $ `sphereEquiv` composed with the radial blow-up of the open unit
ball). In place of $\deg(aqc) = 1$, `aqc_homotopic_id` proves
$aqc \simeq \mathrm{id}$, since $P_{z,r} c \simeq \mathrm{id}$
(`pinch_comp_c_homotopic`); no degree is defined. Persistence of
orientation preservation is `LocalAction.orientationPreserving_restrict`.

## Sources

- [Preprint source map: `lem:averaged-test`](../../sources/preprint.md)

## Depends on

- [Collapse and compactification](collapse.md)

## Proof depends on

- [Collapse and compactification](collapse.md)
