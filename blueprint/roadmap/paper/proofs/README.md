---
article_id: af_a3a41b7e1d0a3b48c3e0cf48
---

# The main theorems

This chapter states the two results of the paper and assembles their proofs from the local data, the theorems of the construction chapters, and the cited inputs. Both theorems rest on open statements, and each final proof names the ones it uses. $p$-adic exclusion rests on Newman's theorem on fixing an open set, lifting, the two sides of an excision boundary, Lemma U and idempotent splitting; Hilbert–Smith rests on these and also on Newman's theorem on small orbits, the embedding of $\mathbb Z_p$ in a compact torsion-free group and the Gleason–Yamabe theorem. An $n$-manifold is a Hausdorff space with an atlas onto open subsets of $\mathbb{R}^n$, with no countability assumption, and connected spaces are nonempty.

## $p$-adic exclusion

The first theorem says that $\mathbb{Z}_p$ never acts faithfully on a connected manifold. Its proof has two halves.

- [$p$-adic exclusion](padic-exclusion.md)

The first half moves a faithful action into one chart. A point with no fixed neighbourhood, from the chapter on [local data](../local-data/README.md), is saturated by a small subgroup; the kernel of the saturated action is a closed subgroup that would fix a neighbourhood of the point, so it is zero. The result is a faithful action on a connected open subset of $\mathbb{R}^n$, and second countability is never needed.

- [Reduction to one chart](one-chart.md)

The second half excludes such an action. Fixed local data for it give a control space $T$, a compact metric space with a free isometric $C_p$-action, possibly empty, and one cube parameter $s$ fixes the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md), which needs no control space. [Theorem C](../compression/theorem-c.md) compresses the labelled chain models of the torus test map into a strict Poincaré complex over $T\times S^n$ whose image after forgetting $T$ is the class of the torus test map, and [Theorem B for the test map](../evaluation/theorem-b-test-map.md) makes the [tail signature](../signatures/tail/tail-signature.md) of that class's iterated cut eventually $\pm1$. If $T$ is empty, the complex is zero, so the tail is zero, which is absurd. Otherwise the data form [standing data](../corner/standing-data.md), Theorem C adds a graph-type homotopy action, and [Theorem A](../corner/theorem/theorem-a.md), whose arithmetic core is [divisibility of the signature tail](../divisibility/divisibility.md), makes the same tail eventually divisible by $p$. No integer sequence does both.

- [Local exclusion](local-exclusion.md)
- [Integer tails](integer-tails.md)

## Manifolds with boundary

For a manifold with boundary we pass to its intrinsic interior: the points with a neighbourhood homeomorphic to an open subset of $\mathbb{R}^n$. It needs no atlas, so every homeomorphism preserves it; it is open, dense and connected, and an action restricts to it faithfully.

- [Intrinsic interior](intrinsic-interior.md)
- [The intrinsic interior is open](intrinsic-interior-open.md)
- [The intrinsic interior is charted](intrinsic-interior-charted.md)
- [The intrinsic interior is invariant](intrinsic-interior-invariant.md)
- [The intrinsic interior is dense](intrinsic-interior-dense.md)
- [The intrinsic interior is connected](intrinsic-interior-connected.md)
- [The action on the intrinsic interior](interior-action.md)
- [The restricted action is continuous](interior-action-continuous.md)
- [The restricted action is faithful](interior-action-faithful.md)
- [$p$-adic exclusion with boundary](padic-exclusion-boundary.md)

## Hilbert–Smith

A group acting faithfully on a $T_1$ space is Hausdorff, so the group need not be assumed Hausdorff.

- [Faithful actions give Hausdorff groups](faithful-hausdorff.md)

Near the identity the group has no nontrivial subgroups. Take a compact neighbourhood of the identity that moves one chart ball less than Newman's constant. The closure of a subgroup inside it is compact. An element of prime order there would have small orbits, so Newman's theorem, from the appendix on [Newman's theorem](../inputs/newman/README.md), makes it trivial. Without torsion, a nontrivial closure would contain a copy of $\mathbb{Z}_p$, by the appendix on [compact groups](../inputs/compact-groups/README.md), and $p$-adic exclusion forbids that.

- [A faithfully acting group has no small subgroups](no-small-subgroups.md)

The Gleason–Yamabe theorem, from the appendix on [Gleason–Yamabe](../inputs/gleason-yamabe/README.md), turns this into a Lie group structure, and the intrinsic interior handles the boundary once more.

- [Hilbert–Smith](hilbert-smith.md)
- [Hilbert–Smith with boundary](hilbert-smith-boundary.md)
