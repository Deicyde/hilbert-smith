---
article_id: af_d7786de054afb8354874b1de
declaration: lemma
origin: cited
---

# Homotopy extension

Let $Y_0$ be compact metrizable, $F_0 \subset Y_0$ closed, and
$f : Y_0 \to S^d$ continuous. Every homotopy
$H : F_0 \times [0,1] \to S^d$ starting at $f|_{F_0}$ extends to a
homotopy on $Y_0$ starting at $f$.

*Proof sketch.* Paste $H$ with $f$ on the closed subset
$(F_0 \times I) \cup (Y_0 \times \{0\})$, extend coordinates by
Tietze, normalize where the extension is large, and damp the time
parameter by a cutoff function equal to $1$ on $F_0$ and $0$
outside the good neighborhood.

## Sources

- [Preprint source map: `top:neighborhood-extension`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.
