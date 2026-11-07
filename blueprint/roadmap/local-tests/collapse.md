---
article_id: af_e2de11f27208c9347c2a8a7f
declaration: lemma
origin: cited
lean: HilbertSmith.continuous_collapse HilbertSmith.continuousSMul_onePoint HilbertSmith.osmul_infty HilbertSmith.compactSpace_onePoint HilbertSmith.metrizableSpace_onePoint HilbertSmith.compactSpace_orbitQuotient HilbertSmith.metrizableSpace_orbitQuotient HilbertSmith.Interface.collapseInput
statement: formalized
proof: formalized
---

# Collapse and compactification

With $W = O \times \R^{d-n} \subset \R^d$ carrying the product
action (trivial in the added coordinates), the collapse map
$c : S^d \to W^+$ sending $W$ identically and everything else to
$\infty$ is continuous. The action extends jointly continuously to
$W^+$ fixing $\infty$. Both $W^+$ and its orbit space by any
closed subgroup of $G$ are compact metrizable.

*Proof sketch.* Inverse images of basic neighborhoods are open on
both sides. Saturation of compacts gives joint continuity at
$\infty$. Averaging a compatible metric over $G$ and minimizing
over orbits produces compatible (quotient) metrics.

*Formalization.* The statements above are about a multiplicative action.
`HilbertSmith.Interface.collapseInput` transports the two that the
contradiction uses, the extension to $W^+$ and the metrizability of the
orbit space, to the additive action of $\Zp$ through `Multiplicative`.

## Sources

- [Preprint source map: `lem:collapse`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.
