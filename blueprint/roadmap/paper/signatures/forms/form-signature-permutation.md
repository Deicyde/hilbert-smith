---
article_id: af_ee19c9c0fbab330ec8f8ab24
declaration: lemma
origin: bridged
---

# Permutation tensor rule

Let $(W,b,\rho)$ be as in [the existence lemma](../l-four/signature-splitting-exists.md): $W$ finite-dimensional, $b$ nondegenerate symmetric and $\rho$ an action of a finite group $G$ by $b$-isometries. Let $X$ be a finite $G$-set and $s_X$ the standard form on $\mathbb R[X]$. Then $\mathrm{sign}_{s_X\otimes b}(g)=|X^g|\,\mathrm{sign}_b(g)$ on $\mathbb R[X]\otimes W$ with the diagonal action.

*Proof sketch.* Take a $G$-invariant splitting $(V^+,V^-)$ of $W$ (existence lemma). Then $(\mathbb R[X]\otimes V^+,\mathbb R[X]\otimes V^-)$ is a splitting, since a positive definite form tensored with a definite form is definite of the same sign (use orthonormal bases). The trace of a tensor product is the product of the traces, and the trace of a permutation matrix is its number of fixed points.

## Sources

- HS paper, Section 3

## Depends on

- [Independence](../l-four/signature-splitting-independence.md)
- [Invariant signature splittings exist](../l-four/signature-splitting-exists.md)
