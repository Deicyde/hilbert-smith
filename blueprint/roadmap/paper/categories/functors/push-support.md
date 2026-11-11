---
article_id: af_cbf0dc361a9984881eb8bf2c
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.push_supp
---

# Pushforward preserves support

Let $f:X\to X'$ be equivariant and continuous, and let $S\subset X$ and $S'\subset X'$ be closed and invariant with $f(S)\subset S'$. Then $f_*$ carries $\mathcal A_S$ into $\mathcal A_{S'}$.

The statement needs neither that $S$ and $S'$ are closed nor that they are invariant.

*Proof sketch.* $f$ is uniformly continuous on compact $X$. For $\varepsilon>0$ take $\delta$. If $d(x,s)<\delta$ with $s\in S$, then $d(fx,fs)<\varepsilon$ and $fs\in S'$.

## Sources

- HS paper, Section 2

## Depends on

- [Pushforward](pushforward.md)
- [Support subcategory](../supports/support-subcategory.md)
