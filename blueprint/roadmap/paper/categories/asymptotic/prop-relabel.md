---
article_id: af_4718c82ef7c7cad9779e3fdf
declaration: lemma
origin: bridged
---

# Relabelling changes propagation by the labelling errors

Let $B,B'$ be finite sets with labellings $\ell,m:B\to X$ and $\ell',m':B'\to X$. Then for $u\in\mathbb Q^{B'\times B}$,
$$\operatorname{prop}_{m,m'}(u)\le\operatorname{prop}_{\ell,\ell'}(u)+\max_{b}d(\ell b,mb)+\max_{b'}d(\ell'b',m'b'),$$
where an empty maximum is $0$.

*Proof sketch.* Take a nonzero entry $u_{b'b}$. Then $d(m'b',mb)\le d(m'b',\ell'b')+d(\ell'b',\ell b)+d(\ell b,mb)$.

## Sources

- HS paper, Section 2

## Depends on

- [Propagation](propagation.md)
