---
article_id: af_fce8de43cea1c0a3fb088039
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.padicExclusion_boundary
---

# $p$-adic exclusion with boundary

Let $p$ be a prime, $n\ge1$, and let $M$ be a connected Hausdorff space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n: x_0\ge0\}$, with no countability assumption. Then no jointly continuous action of $\mathbb{Z}_p$ on $M$ is faithful.

*Proof sketch.* Suppose the action is faithful, and let $M^\circ_n$ be the intrinsic interior.
1. $M^\circ_n$ is connected, hence nonempty, it is Hausdorff as a subspace of $M$, and it carries an atlas onto open subsets of $\mathbb{R}^n$.
2. The action restricts to a jointly continuous action on $M^\circ_n$, which is faithful because $M^\circ_n$ is dense.
3. This contradicts $p$-adic exclusion for $M^\circ_n$.

This theorem rests, through $p$-adic exclusion, on the open statements [Newman's theorem on fixing an open set](../inputs/newman/newman-open-set.md), [lifting](../l-theory/localization/boundary/lift-to-pair.md) (through every cut boundary and the tail signature), [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md) (through the inner cuts of Theorem B), [Lemma U](../l-theory/comparison/lemma-u.md) (through the tail signature) and [idempotent splitting in the bounded homotopy category](../corner/theorem/kb-idempotent-splitting.md) (through Theorem A).

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, dimension 0 and boundary)
- New: the interior reduction uses the intrinsic interior, so that no local homology is needed

## Depends on

## Proof depends on

- [Intrinsic interior](intrinsic-interior.md)
- [The intrinsic interior is charted](intrinsic-interior-charted.md)
- [The intrinsic interior is connected](intrinsic-interior-connected.md)
- [The action on the intrinsic interior](interior-action.md)
- [The restricted action is continuous](interior-action-continuous.md)
- [The restricted action is faithful](interior-action-faithful.md)
- [$p$-adic exclusion](padic-exclusion.md)
