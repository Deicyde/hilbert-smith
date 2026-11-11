---
article_id: af_7404c67e48e4a3e990aad474
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_zero_left
---

# A product of structures with a zero left factor

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees. The [product of structures](based-str-prod.md) $0\otimes\theta$ of the zero structure of $C$ with any $\theta\in M(E)_{m'}$ is $0$.

*Proof sketch.* Every block of $0\otimes\theta$ is, up to sign and transport, a Kronecker product with the zero factor $0$ ([Kronecker product with a zero factor](../kron-zero.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)

## Proof depends on

- [Kronecker product with a zero factor](../kron-zero.md)
