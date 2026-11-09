---
article_id: af_38d0b4322aa736cb5e9446f6
declaration: lemma
origin: bridged
---

# Average propagation

Let $I$ be a finite set, $\kappa:I\to G_i$, $\lambda:I\to\mathbb Q$, and let each $u_k$ ($k\in I$) have graph type $\chi_i(\kappa k)$ with bound $\delta$. Then $\sum_{k\in I}\lambda_k\operatorname{Ind}_{\kappa k}u_k$ is equivariant with propagation at most $\delta$. The bound does not depend on $|I|$ or $q_i$.

*Proof sketch.*
1. [Sheet translation](sheet-translation.md) bounds each term.
2. Propagation of a sum is at most the maximum over its terms, and scalars do not increase it.

## Sources

- HS paper, Sections 2 and 11.
- New: indexed by a finite set over $G_i$, so the single sums ($I=G_i$, $\kappa=\mathrm{id}$) and the pair sums ($I=G_i^2$, $\kappa(g,h)=gh$) are both instances.

## Depends on

- [Sheet translation](sheet-translation.md)

## Proof depends on

- [Propagation of a sum](../../categories/asymptotic/prop-add.md)
- [Propagation of a scalar multiple](../../categories/asymptotic/prop-smul.md)
