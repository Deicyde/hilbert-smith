---
article_id: af_2e5e1cd05bac9e981f176907
---

# Compression

Fix [fixed local data](../local-data/control/fixed-local-data.md) with buffers $r<R<t<u$, and put $t'=(t+u)/2$; the [exterior](../corner/exterior.md) $Z_0$ is that of $n$ and $R$, and $Z=T\times Z_0$ for the control space $T$, which may be empty. At level $i$ the [chain model](../chain-models/grid/chain-model.md) $D_i$ is cut down to the cells whose closed cubes meet $K_t=f_T^{-1}(\overline B(0,t))$. The discarded cells span a subcomplex, so the compressed complex $C$ inherits a differential and every structure map. Retained cells, and the discarded cells that one matrix of the chain-model estimates can reach from them, lie in the [buffered cells](../chain-models/grid/buffered-cells.md) $\mathcal B_i(u)$, where the [control labels](../chain-models/grid/control-labels.md) $\lambda$ are defined through $\pi$; nothing else needs a label. Every defect of compression is a word $\alpha\,Q\,\beta$ through a discarded cell. The [endpoint lemma](endpoint-lemma.md) factors such a word through discarded buffered cells, whose labels lie in $Z$. This gives [Theorem C](theorem-c.md), whose last clause identifies the scalar image with the [germ](../evaluation/germ.md) of the torus test map.

Articles, in reading order: [retained cells](retained-cells.md), [discarded subcomplex](discarded-subcomplex.md), [buffers hold eventually](buffer-eventually.md), [start index](start-index.md), [compressed complex](compressed-complex.md), [compressed maps](compressed-maps.md), [product rule](compression-product-rule.md), [compressed differential](compressed-differential.md), [residual identities](compressed-residuals.md), [endpoint lemma](endpoint-lemma.md), [compressed Poincaré](compressed-poincare.md), [compressed action](compressed-action.md), [scalar image](compressed-scalar-image.md), [Theorem C](theorem-c.md).

## Sources
- HS paper, Section 10, and the closing estimates of Section 9.
