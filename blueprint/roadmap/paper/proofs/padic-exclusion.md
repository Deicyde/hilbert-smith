---
article_id: af_7e35ccf432aefaf0cfe4c81f
declaration: theorem
origin: bridged
---

# $p$-adic exclusion

Let $p$ be a prime, $n\in\mathbb N$, and let $X$ be a connected $n$-manifold: a connected Hausdorff space with an atlas of charts onto open subsets of $\mathbb{R}^n$, with no countability assumption. Let $\mathbb{Z}_p$ act on $X$ with $(a,x)\mapsto a\cdot x$ jointly continuous. Then the action is not faithful: there are $a\ne b$ in $\mathbb{Z}_p$ with $a\cdot x=b\cdot x$ for all $x\in X$.

*Proof sketch.* Suppose the action is faithful. The reduction to one chart gives a faithful jointly continuous action of $\mathbb{Z}_p$ on a nonempty connected open subset of $\mathbb{R}^n$, and local exclusion says that no such action exists.

This theorem rests on the open statements that the reduction to one chart and local exclusion rest on: Newman's theorem on fixing an open set, and those behind Theorems A and B.

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Theorem 1.1, the boundaryless case)
- [OpenAI preprint, Section 6](../../../sources/preprint.md#section-6-character-classes-sections06-character-classestex), 06-character-classes.tex lines 502-516

## Depends on

## Proof depends on

- [Reduction to one chart](one-chart.md)
- [Local exclusion](local-exclusion.md)
