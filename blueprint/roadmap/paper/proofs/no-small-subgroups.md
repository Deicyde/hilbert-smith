---
article_id: af_fc2488f4bac3234fd975aaa3
declaration: theorem
origin: bridged
---

# A faithfully acting group has no small subgroups

Let $G$ be a locally compact topological group acting jointly continuously and faithfully on a connected $n$-manifold $M$, with no countability assumption on $M$ or $G$ and no separation assumption on $G$. Then some neighbourhood of $1$ in $G$ contains no subgroup other than $\{1\}$.

*Proof sketch.*
1. $G$ is Hausdorff, because faithful actions give Hausdorff groups.
2. $M$ is nonempty. Composing a chart with a translation and a dilation gives an open partial homeomorphism $e$ from $M$ to $\mathbb{R}^n$ whose target contains the closed unit ball $\bar B$. Write $e^{-1}(S)$ for the image of $S\subseteq\bar B$ under the inverse of $e$; then $C=e^{-1}(\bar B)$ is compact. Take $\delta$ from Newman's theorem on small orbits for $M$ and $e$.
3. Uniformly small displacement near the identity, for $C$ and $\delta$, gives a neighbourhood $V$ of $1$, and local compactness a compact neighbourhood $W\subseteq V$.
4. Let $H\subseteq W$ be a subgroup. Its closure $K$ is a subgroup inside the closed set $W$, so $K$ is compact and Hausdorff.
5. If $K$ has an element $g\ne1$ of finite order $m$, take a prime $q\mid m$ and put $h=g^{m/q}$, of order $q$. All powers of $h$ lie in $K\subseteq W$, so Newman's theorem on small orbits makes $h$ fix the nonempty open set $e^{-1}(B)$, and Newman's theorem on fixing an open set makes $h$ act trivially. Faithfulness gives $h=1$, a contradiction.
6. So $K$ has no nontrivial element of finite order. If $K\ne1$, the embedding theorem gives a prime $p$ and a continuous injective homomorphism $\mathbb{Z}_p\to K\subseteq G$. Restricting the action along it gives a faithful jointly continuous action of $\mathbb{Z}_p$ on $M$, against $p$-adic exclusion. Hence $K=1$ and $H=1$.

Steps 2-5 use only one chart ball and no metric on $M$, so the argument holds for $M$ that is not second countable.

## Sources

- New: the assembly; a small subgroup has a compact closure inside $W$, which either has an element of prime order (excluded by Newman's theorem) or is torsion-free (excluded through $\mathbb{Z}_p$ and $p$-adic exclusion)
- Published: T. Tao, Hilbert's fifth problem and related topics, the classical reduction through Newman's theorem (citation not checked against the book)
- [OpenAI preprint, Section 6](../../../sources/preprint.md#section-6-character-classes-sections06-character-classestex), 06-character-classes.tex lines 518-527 (cites the classical reduction; the route differs)
- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Corollary 1.2, by a different route through compact Lie subgroups and the structure theorem)

## Depends on

## Proof depends on

- [Faithful actions give Hausdorff groups](faithful-hausdorff.md)
- [Uniformly small displacement near the identity](../local-data/subgroups/small-displacement.md)
- [Newman's theorem: small orbits](../inputs/newman/newman-small-orbits.md)
- [Newman's theorem: fixing an open set](../inputs/newman/newman-open-set.md)
- [$\mathbb Z_p$ inside a compact torsion-free group](../inputs/compact-groups/zp-in-torsion-free.md)
- [$p$-adic exclusion](padic-exclusion.md)
