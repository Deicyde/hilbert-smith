---
article_id: af_4718c82ef7c7cad9779e3fdf
declaration: lemma
origin: bridged
---

# Relabelling changes propagation by the labelling errors

Let $B,B'$ be finite sets with labellings $\lambda,\mu:B\to X$ and $\lambda',\mu':B'\to X$. Then for $u\in\mathbb Q^{B'\times B}$,
$$\operatorname{prop}_{\mu,\mu'}(u)\le\operatorname{prop}_{\lambda,\lambda'}(u)+\max_{b}d(\lambda b,\mu b)+\max_{b'}d(\lambda'b',\mu'b'),$$
where an empty maximum is $0$.

*Proof sketch.* Take a nonzero entry $u_{b'b}$. Then $d(\mu'b',\mu b)\le d(\mu'b',\lambda'b')+d(\lambda'b',\lambda b)+d(\lambda b,\mu b)$.

## Sources

- HS paper, Section 2

## Depends on

- [Propagation](propagation.md)
