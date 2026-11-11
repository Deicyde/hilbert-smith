---
article_id: af_6d206c00c36f4bf4e3569d5b
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.dense_pos_halfSpace
---

# The open half-space is dense in the half-space

Let $n\ge1$. The open half-space $\{x\in\mathbb{R}^n:x_0>0\}$ is dense in the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$, with the subspace topology.

*Proof sketch.* The half-space is convex with nonempty interior $\{x_0>0\}$ in $\mathbb{R}^n$, so it lies in the closure of that interior. The closure of a subset of the half-space, taken in the half-space, is the trace of its closure in $\mathbb{R}^n$.

## Sources

- Standard; split out of the proofs that the intrinsic interior is dense and connected.

## Depends on
