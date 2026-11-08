---
article_id: af_ae953417fe55e04c4cac64f9
declaration: lemma
origin: cited
lean: HilbertSmith.Interface.averagedTest HilbertSmith.Interface.aqc_homotopic_id HilbertSmith.Interface.LocalAction.pinch HilbertSmith.Interface.LocalAction.pinch_comp_c_homotopic HilbertSmith.Interface.LocalAction.orientationPreserving_restrict HilbertSmith.Interface.LocalAction.restrict_faithful
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

*Remark.* The pinch can be chosen with $P_{z,r}c$ homotopic to the
identity of $S^d = \R^d \cup \{\infty\}$. Let
$P_{z,r}(w) = P((w - z)/r)$ and $P_{z,r}(\infty) = \infty$, where
$P$ maps the open unit ball onto $\R^d$ by the radial blow-up
$u \mapsto u/(1 - \lvert u\rvert)$ and sends every other point to
$\infty$. Since $\overline B(z, r) \subset W$, the composite
$P_{z,r}c$ is $v \mapsto P((v - z)/r)$ on all of $\R^d$, fixing
$\infty$. Deform $P$ in this formula through the maps
$u \mapsto u/(1 - s\lvert u\rvert)$ on $\lvert u\rvert < 1/s$, with
value $\infty$ elsewhere, as $s$ decreases from $1$ to $0$; then
move $z$ to $0$ and $r$ to $1$. This gives
$P_{z,r}c \simeq \mathrm{id}$, hence $aqc \simeq \mathrm{id}$, which
implies $\deg(aqc) = 1$.

## Sources

- [Preprint source map: `lem:averaged-test`](../../sources/preprint.md)

## Depends on

- [Collapse and compactification](collapse.md)

## Proof depends on

- [Collapse and compactification](collapse.md)
