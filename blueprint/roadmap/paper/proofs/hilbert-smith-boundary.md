---
article_id: af_4796f2c2d5509fee76b295c9
declaration: theorem
origin: bridged
---

# Hilbert–Smith with boundary

Let $n\ge1$, let $M$ be a connected Hausdorff space with an atlas of charts onto open subsets of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$, and let $G$ be a locally compact topological group acting jointly continuously and faithfully on $M$. Then there are $d\in\mathbb{N}$ and an atlas on $G$ of charts that are homeomorphisms, for the given topology of $G$, from open subsets of $G$ onto open subsets of $\mathbb{R}^d$, whose transition maps are $C^\infty$ and for which multiplication and inversion are $C^\infty$. Neither $M$ nor $G$ is assumed second countable, and $G$ is not assumed Hausdorff.

*Proof sketch.* The intrinsic interior $M^\circ_n$ is dense and connected and carries the subspace atlas, so it is a connected $n$-manifold. $G$ acts on it jointly continuously, and faithfully because it is dense. Apply Hilbert–Smith to $M^\circ_n$.

This theorem rests, through Hilbert–Smith, on the open statements [Gleason–Yamabe](../inputs/gleason-yamabe/gleason-yamabe.md) (directly in Hilbert–Smith); [Newman's theorem on small orbits](../inputs/newman/newman-small-orbits.md), [$\mathbb Z_p$ inside a compact torsion-free group](../inputs/compact-groups/zp-in-torsion-free.md) and [Newman's theorem on fixing an open set](../inputs/newman/newman-open-set.md) (through the absence of small subgroups); and, through $p$-adic exclusion, [lifting](../l-theory/localization/boundary/lift-to-pair.md) (through every cut boundary and the tail signature), [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md) (through the inner cuts of Theorem B), [Lemma U](../l-theory/comparison/lemma-u.md) (through the tail signature) and [idempotent splitting in the bounded homotopy category](../corner/theorem/kb-idempotent-splitting.md) (through Theorem A).

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Corollary 1.2)

## Depends on

## Proof depends on

- [Intrinsic interior](intrinsic-interior.md)
- [The intrinsic interior is charted](intrinsic-interior-charted.md)
- [The intrinsic interior is dense](intrinsic-interior-dense.md)
- [The intrinsic interior is connected](intrinsic-interior-connected.md)
- [The action on the intrinsic interior](interior-action.md)
- [The restricted action is continuous](interior-action-continuous.md)
- [The restricted action is faithful](interior-action-faithful.md)
- [Hilbert–Smith](hilbert-smith.md)
