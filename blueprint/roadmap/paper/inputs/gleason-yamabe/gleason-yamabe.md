---
article_id: af_4eac8636dc0bf73b2d1803c4
declaration: theorem
origin: cited
---

# Gleason–Yamabe: no small subgroups implies Lie

Let $G$ be a Hausdorff locally compact topological group with no small subgroups: some neighbourhood of $1$ contains no subgroup other than $\{1\}$. Then there are $d\in\mathbb N$ and an atlas on $G$ of charts that are homeomorphisms, for the given topology of $G$, from open subsets of $G$ onto open subsets of $\mathbb R^d$, whose transition maps are $C^\infty$ and for which multiplication and inversion are $C^\infty$. No countability is assumed.

**Remark (not formalized).** This is an open statement: the Lean states it now and proves it later. Planned route. The route is the classical one; an outline, after T. Tao, Hilbert's fifth problem and related topics, and I. Goldbring's notes (chapter numbers not checked):
1. A neighbourhood with no small subgroups yields an escape norm. Convolution against Haar measure improves it to a Gleason norm, which satisfies the escape and commutator estimates.
2. In a group with a Gleason norm, the one-parameter subgroups form a real vector space $L(G)$ under limits of $g_\varepsilon^{\lfloor t/\varepsilon\rfloor}$. This space is locally compact, hence finite-dimensional.
3. The exponential map $L(G)\to G$ is a homeomorphism from a neighbourhood of $0$ onto a neighbourhood of $1$. Injectivity comes from escape; surjectivity onto a neighbourhood comes from the Gleason estimates.
4. The adjoint action and Baker–Campbell–Hausdorff-type control give smooth, indeed analytic, multiplication in exponential coordinates, whose translates form the atlas. Equivalently, apply Cartan's closed-subgroup theorem to the image of the adjoint representation and treat its kernel separately.

## Sources

- [HS paper, Section 13](../../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (proof of Corollary 1.2, citing Gleason and Yamabe)
- [OpenAI preprint, Section 1](../../../../sources/preprint.md#section-1-introduction-sections01-introductiontex), 01-introduction.tex lines 62-66
- Published: A. M. Gleason, Groups without small subgroups, Ann. of Math. 56 (1952); H. Yamabe, A generalization of a theorem of Gleason, Ann. of Math. 58 (1953) (not checked against the originals)

## Depends on
