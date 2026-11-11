---
article_id: af_87b8381fb104ae61710475be
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.separation
---

# Separation

Let $X$ be compact with an isometric $C_p$-action. If $S,Z\subset X$ are disjoint closed invariant sets, the quotient functor restricted to $\mathcal A_S\to\mathcal A_{\mathbf G}(X)/\mathcal A_Z$ is fully faithful.

*Proof sketch.* Fullness holds because the functor is a quotient. Disjoint compact sets have disjoint $\delta$-thickenings for some $\delta>0$. A map between $S$-supported objects that factors through $\mathcal A_Z$ has, by the [support ideal](support-ideal.md), entries whose endpoints are eventually near both $S$ and $Z$, so it is eventually zero.

## Sources

- HS paper, Section 2

## Depends on

- [Support filtration](support-filtration.md)

## Proof depends on

- [Maps through a disjoint support vanish](disjoint-support-vanishing.md)
