---
article_id: af_4a900deaec2cdf778e52fbc7
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.faithfulSMul_intrinsicInterior
---

# The restricted action is faithful

Let $n\ge1$, let $M$ be a Hausdorff space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$, and let a group $G$ act faithfully on $M$, each element acting by a continuous map. Then the restricted action of $G$ on $M^\circ_n$ is faithful. The same holds for an action of an additive group.

*Proof sketch.* If $g$ and $g'$ agree on $M^\circ_n$, then the continuous maps $x\mapsto gx$ and $x\mapsto g'x$ into the Hausdorff space $M$ agree on a dense set, hence everywhere, so $g=g'$.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, dimension 0 and boundary)

## Depends on

- [The action on the intrinsic interior](interior-action.md)
- [Intrinsic interior](intrinsic-interior.md)

## Proof depends on

- [The intrinsic interior is dense](intrinsic-interior-dense.md)
