---
article_id: af_df57c005e9d53870860a0788
declaration: theorem
origin: bridged
---

# Hilbert–Smith

Let $M$ be a connected $n$-manifold and let $G$ be a locally compact topological group acting jointly continuously and faithfully on $M$. Then $G$ is a Lie group in the following sense: there are $d\in\mathbb{N}$ and an atlas on $G$ of charts that are homeomorphisms, for the given topology of $G$, from open subsets of $G$ onto open subsets of $\mathbb{R}^d$, whose transition maps are $C^\infty$ and for which multiplication $G\times G\to G$ and inversion are $C^\infty$. Neither $M$ nor $G$ is assumed second countable, and $G$ is not assumed Hausdorff.

*Proof sketch.* $G$ is Hausdorff because faithful actions give Hausdorff groups, and it has no small subgroups. The Gleason–Yamabe theorem gives the conclusion.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Corollary 1.2)
- [OpenAI preprint, Section 6](../../../sources/preprint.md#section-6-character-classes-sections06-character-classestex), 06-character-classes.tex lines 518-527
- Published: T. Tao, Hilbert's fifth problem and related topics, the classical reduction (citation not checked against the book)
- New: the group step goes through Newman's theorem on small orbits, and no structure theorem for $G$ is used

## Depends on

## Proof depends on

- [Faithful actions give Hausdorff groups](faithful-hausdorff.md)
- [A faithfully acting group has no small subgroups](no-small-subgroups.md)
- [Gleason–Yamabe: no small subgroups implies Lie](../inputs/gleason-yamabe/gleason-yamabe.md)
