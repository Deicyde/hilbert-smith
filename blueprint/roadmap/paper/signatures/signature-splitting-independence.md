---
declaration: lemma
origin: bridged
---

# The signature does not depend on the splitting

For any signature splitting $(V'^+,V'^-)$ of $(W,b,\rho)$, $\mathrm{sign}_b(g)=\mathrm{tr}(g|V'^+)-\mathrm{tr}(g|V'^-)$.

*Proof sketch.* Let $(V^+,V^-)$ be the chosen splitting. Then $V'^+\cap V^-=0$, because $b$ is positive on one and negative on the other. So $\dim V'^+\le\dim V^+$, and by symmetry the dimensions are equal. Therefore projection along $V^-$ restricts to a $G$-equivariant isomorphism $V'^+\to V^+$, and conjugation-invariance of the trace equates the traces. The negative parts are handled in the same way.

## Sources

- HS paper, Section 3
- [published: Sylvester 1852, law of inertia] [U]

## Depends on

- [The equivariant signature](form-signature.md)
