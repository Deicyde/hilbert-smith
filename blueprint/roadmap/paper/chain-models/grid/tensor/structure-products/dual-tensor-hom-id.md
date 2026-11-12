---
article_id: af_22b0bc771d6a3e97a611c32e
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedDualTensorHom_id
---

# Dual tensor of identities

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees, and $m+m'=k$. The [dual tensor](../based-dual-tensor-hom.md) $\Xi^{-1}(1\otimes1)\Xi$ of the [identities of degree zero](../../poincare/grid-factor/id-dual-deg0.md) of $C^{m-*}$ and $E^{m'-*}$ is the identity of $(C\otimes E)^{k-*}$.

*Proof sketch.* The block from the summand $p$ to the summand $p$ is $s(a,b)^2=1$ times the Kronecker product of identities, which is the identity ([Kronecker product of identities](../kron-transport.md)); all other blocks vanish. The identity is the sum of its diagonal blocks ([block decomposition of the identity](../block-decomposition.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Dual tensor of graded maps of based complexes](../based-dual-tensor-hom.md)
- [The identity of a dual complex as a map of degree zero](../../poincare/grid-factor/id-dual-deg0.md)

## Proof depends on

- [Kronecker product of identities](../kron-transport.md)
- [Block decomposition of the identity](../block-decomposition.md)
