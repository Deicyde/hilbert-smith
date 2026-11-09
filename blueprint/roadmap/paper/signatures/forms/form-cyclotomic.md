---
article_id: af_8a85052ea02d3d948f876266
declaration: lemma
origin: bridged
---

# Cyclotomic arithmetic

Let $G$ be cyclic of order $p^a$ with $p$ prime and $a\ge1$, and let $g$ generate $G$. If $\mathrm{sign}_b(g)=0$, then $p\mid\dim V^+-\dim V^-$.

*Proof sketch.* Since $g^{p^a}=1$, the trace of $g$ on $V^\pm$ is the sum of the complex roots of its characteristic polynomial, and these roots are $p^a$-th roots of unity. Let $\zeta=e^{2\pi i/p^a}$, let $m_j^\pm$ be the multiplicity of $\zeta^j$ on $V^\pm$, and put $F(t)=\sum_j(m_j^+-m_j^-)t^j\in\mathbb Z[t]$. Then $F(\zeta)=\mathrm{sign}_b(g)=0$. $\Phi_{p^a}$ is the minimal polynomial of $\zeta$ over $\mathbb Q$ and is monic, so $\Phi_{p^a}\mid F$ in $\mathbb Z[t]$ by Gauss's lemma. Evaluating at $1$ gives $p=\Phi_{p^a}(1)\mid F(1)=\dim V^+-\dim V^-$ by [the identity value](form-signature-identity.md).

## Sources

- HS paper, Section 3

## Depends on

- [Value at the identity](form-signature-identity.md)
