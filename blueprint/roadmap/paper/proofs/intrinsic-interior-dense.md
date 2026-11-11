---
article_id: af_f03eb2291a6c978f22c2aeb4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.dense_intrinsicInterior
---

# The intrinsic interior is dense

Let $n\ge1$ and let $M$ be a topological space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$. Then $M^\circ_n$ is dense in $M$.

*Proof sketch.* Let $\varphi$ be a chart with domain $V$. The points of $V$ that $\varphi$ maps into the open half-space $\{x_0>0\}$ form an open set on which $\varphi$ is a homeomorphism onto an open subset of $\mathbb{R}^n$, so they lie in $M^\circ_n$. The open half-space is dense in the half-space, so these points are dense in $V$. The chart domains cover $M$.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, dimension 0 and boundary)

## Depends on

- [Intrinsic interior](intrinsic-interior.md)

## Proof depends on

- [Points over the open half-space are interior](half-space-interior.md)
- [The open half-space is dense in the half-space](open-half-space-dense.md)
