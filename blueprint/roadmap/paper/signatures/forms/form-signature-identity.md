---
article_id: af_3c1213273dea19b98538bedd
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.formSign_one
---

# Value at the identity

Let $(W,b,\rho)$ be as in [the existence lemma](../l-four/signature-splitting-exists.md). For every decomposition $W=V^+\oplus V^-$ with $b$ positive definite on $V^+$ and negative definite on $V^-$, invariant or not, $\mathrm{sign}_b(1)=\dim V^+-\dim V^-$. So this integer does not depend on $G$ or $\rho$.

*Proof sketch.* The trace of the identity is the dimension. Apply [independence](../l-four/signature-splitting-independence.md) for $G$ to an invariant splitting, which exists, and for the trivial group, for which every such decomposition is a signature splitting.

## Sources

- HS paper, Section 3

## Depends on

- [The equivariant signature](form-signature.md)

## Proof depends on

- [Signature splittings](signature-splitting.md)
- [Independence](../l-four/signature-splitting-independence.md)
- [Invariant signature splittings exist](../l-four/signature-splitting-exists.md)
