---
article_id: af_dc5f4bf8861603f872634fb9
declaration: def
origin: bridged
statement: formalized
lean: HSP.Compression.retainedProj
---
# Retained projection

Take [fixed local data](../local-data/control/fixed-local-data.md) with [start index](start-index.md) $i_0$, and let $C$ be the [compressed complex](compressed-complex.md). For $i\ge i_0$, the *retained projection* $\mathrm{pr}_i:D_i\to C_i$ is the based projection onto the span of the [retained cells](retained-cells.md): in each degree it sends the basis vector of a retained cell to the same basis vector of $C_i$, and every other cell to $0$. The *retained inclusion* $\mathrm{in}_i:C_i\to D_i$ is the based inclusion, the transpose of $\mathrm{pr}_i$, and $Q_i=1-\mathrm{in}_i\mathrm{pr}_i$. For $i<i_0$, where $C_i=0$, $\mathrm{pr}_i=0$, $\mathrm{in}_i=0$ and $Q_i=1$. On cochains the corresponding maps are $\mathrm{in}_i^*$, $\mathrm{pr}_i^*$ and $Q_i^*$.

## Sources
- HS paper, Section 10 (the quotient by far simplices).

## Depends on

- [Compressed complex](compressed-complex.md)
- [Retained cells](retained-cells.md)
- [Start index](start-index.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)
