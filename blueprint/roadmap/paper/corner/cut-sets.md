---
article_id: af_0f19252ffe09ce926eb39b4e
declaration: def
origin: bridged
statement: formalized
lean: HSP.Corner.cutA
---

# The cut sets

Let $n\ge1$ and $s>0$. In the [round sphere](round-sphere.md) $S^n=\mathbb R^n\cup\{\infty\}$, with the [cube faces](cut-face.md) $B_m$ and their [boundaries](cut-face-boundary.md) $Y_m$ ($Y_0=S^n$), the *cut sets* are, for $1\le m\le n$, $A_m=\overline{Y_{m-1}\setminus B_m}$, the closure in $S^n$. The flag also uses the points [$y_+$](cut-point-plus.md) and [$y_-$](cut-point-minus.md). The definitions do not need $n\ge1$ or $s>0$; the range $1\le m\le n$ is a hypothesis of the results about the cut sets, not of the definitions.

## Sources

- New: the cube-face flag replaces the ball and hemisphere flag of HS paper, Section 12. The cut sets depend only on $n$ and $s$.

## Depends on

- [The round sphere](round-sphere.md)

## Proof depends on

- [The boundary of the cube face](cut-face-boundary.md)
- [The cube face](cut-face.md)
