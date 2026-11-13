---
article_id: af_87cb3f0551da4252773138b8
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.exists_nearestPoint
---

# Nearest-point maps

Let $X$ be a compact metric space and $S\subseteq X$ a nonempty closed subset. Then there is a map $\rho:X\to S$ with $d(x,\rho x)=d(x,S)$ for every $x\in X$.

*Proof sketch.* $S$ is compact, being closed in a compact space, and nonempty, so the continuous function $y\mapsto d(x,y)$ attains its infimum $d(x,S)$ on $S$. Choose $\rho x$ to be such a point.

## Sources

- New: the distance to a nonempty compact set is attained.

## Depends on

- None: metric spaces.
