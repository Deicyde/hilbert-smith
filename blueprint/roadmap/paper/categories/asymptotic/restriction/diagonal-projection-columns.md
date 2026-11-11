---
article_id: af_0e8ec527fa9625cc5f9c5da9
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.AsymPre.trunc_comp_eq
---

# Factorization through a diagonal projection, columns

Let $u:M\to N$ be a sequence of matrices such that, for every $i$, every nonzero entry of $u_i$ lies in a column $(g,k)$ with $P(i,k)$. Then $u\,p_P=u$ for the [diagonal coordinate projection](diagonal-projection.md) $p_P$ of $M$.

*Proof sketch.* Multiplying by $p_P$ on the right kills exactly the columns outside $P$, which vanish.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Diagonal coordinate projection](diagonal-projection.md)
