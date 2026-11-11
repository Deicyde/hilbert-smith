---
article_id: af_1a0e78e8013db101e14e8b59
declaration: theorem
origin: cited
statement: formalized
lean: HSP.newman_open_set
---

# Newman's theorem: fixing an open set

Let $M$ be a connected $n$-manifold: a connected Hausdorff space with an atlas of charts onto open subsets of $\mathbb R^n$, with no countability assumption. Let $f\colon M\to M$ be a homeomorphism with $f^k=\mathrm{id}$ for some $k\ge1$. If $f$ fixes every point of some nonempty open set $U\subseteq M$, then $f=\mathrm{id}$.

**Remark (not formalized).** This is an open statement: the Lean states it now and proves it later. Planned route. (1) Reduce to prime order: if $f\ne\mathrm{id}$ has order $m>1$, take a prime $q\mid m$; then $f^{m/q}$ has order $q$ and still fixes $U$. (2) For $g$ of prime order $q$, Smith theory with $\mathbb Z/q$ coefficients [U] makes the fixed set a $\mathbb Z/q$-cohomology manifold whose local dimension is locally constant; where it contains an open set that dimension is $n$, and a fixed set of dimension $n$ in a connected $n$-manifold is open and closed, hence everything. (3) The argument is local in sheaf cohomology, so it should need no countability; that has not been checked against a published proof.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 23-29
- [OpenAI preprint, Section 1](../../../../sources/preprint.md#section-1-introduction-sections01-introductiontex), 01-introduction.tex lines 119-123
- [HS paper, Section 13](../../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (uses the form for compact Lie groups)
- Published: M. H. A. Newman, A theorem on periodic transformations of spaces, Quart. J. Math. 2 (1931) (not checked against the original)
- Published: J. Pardon, Totally disconnected groups (not) acting on two-manifolds, in Breadth in Contemporary Topology (2019), author manuscript pp. 2-3 (not checked against the original)

## Depends on
