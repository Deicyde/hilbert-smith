---
article_id: af_f3db3b71b83043eefb56ae44
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.ChainModels.Torus.continuousAt_lift
---

# Continuity of the lift

The lift $x\mapsto\tilde x$ is continuous at every $x\in\mathbb T^n$ with $d_\infty(x,0)<2$.

*Proof sketch.* No coordinate of such $x$ is the seam $2=-2$, and away from the seam the representative in $[-2,2)$ depends continuously on the point of the circle.

## Sources

- New: the torus closing of the chart cube $[-2,2]^n$.

## Depends on

- [The lift](lift.md)
