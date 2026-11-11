---
article_id: af_16275cf19bd6fdc02444d44f
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.formSign_eq_of_splitting
---

# The signature does not depend on the splitting

Let $W$ be a finite-dimensional real vector space, $b$ a bilinear form on $W$ and $\rho$ an action of a monoid $G$ on $W$ by linear maps. For any signature splitting $(V'^+,V'^-)$ of $(W,b,\rho)$, $\mathrm{sign}_b(g)=\mathrm{tr}(g|V'^+)-\mathrm{tr}(g|V'^-)$. Symmetry and nondegeneracy of $b$ and finiteness of $G$ (or $G$ being a group) are not needed.

*Proof sketch.* Let $(V^+,V^-)$ be the chosen splitting. Then $V'^+\cap V^-=0$, because $b$ is positive on one and negative on the other. So $\dim V'^+\le\dim V^+$, and by symmetry the dimensions are equal. Therefore projection along $V^-$ restricts to a $G$-equivariant isomorphism $V'^+\to V^+$, and conjugation-invariance of the trace equates the traces. The negative parts are handled in the same way.

## Sources

- HS paper, Section 3
- [Sylvester 1852, law of inertia](../../../../sources/paper/sylvester-1852.md) [U]

## Depends on

- [Signature splittings](../forms/signature-splitting.md)
- [The equivariant signature](../forms/form-signature.md)
