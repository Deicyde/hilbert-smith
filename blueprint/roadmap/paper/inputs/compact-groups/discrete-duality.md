---
article_id: af_f07c6a62dd770135b924db08
declaration: theorem
origin: background
not_ready: true
---

# Characters of the dual of a discrete group

Let $D$ be a commutative group, and give the group $\widehat D$ of homomorphisms $D\to\mathbb T$ the topology of pointwise convergence. Every continuous homomorphism $\Lambda\colon\widehat D\to\mathbb T$ is evaluation $\lambda\mapsto\lambda(d)$ at some $d\in D$.

Remark (not formalized). This is an open statement: the Lean states it now and proves it later. Planned route. The evaluations span a self-adjoint unital subalgebra of the continuous complex functions on the compact group $\widehat D$. It separates points by definition, so the Stone–Weierstrass theorem makes it dense. Distinct characters are orthogonal for the Haar probability measure. A $\Lambda$ that is not an evaluation would therefore be orthogonal to itself, which is impossible since $|\Lambda|=1$.

## Sources

- Published: G. B. Folland, A Course in Abstract Harmonic Analysis, Pontryagin duality in Chapter 4 (theorem numbers not checked)

## Depends on
