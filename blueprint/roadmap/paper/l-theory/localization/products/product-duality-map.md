---
article_id: af_71c7adf652a3fbee5acacca3
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.strProd_toHom
---

# Duality map of a product

Let $C$, $E$, $\phi\in M(C)_m$ and $\theta\in M(E)_n$ be as in [External product of structures](external-product.md), with $\partial\phi=0$ and $\partial\theta=0$, and suppose $\phi\otimes\theta$ is a cycle (it is, by the Leibniz rule). Then
$$(\phi\otimes\theta)_\natural=(\phi_\natural\otimes\theta_\natural)\circ\Xi,$$
where $\Xi$ is the isomorphism of [Dual of a tensor product](product-dual-iso.md) and $\phi_\natural\otimes\theta_\natural$ is the tensor of chain maps of [Tensor product of complexes](complex-product.md).

*Proof sketch.* Read the definition of $\phi\otimes\theta$ block by block: on the summand $(C_{m-a}\boxtimes E_{n-b})^*$ both sides are $s(a,b)\,(\phi_a\boxtimes\theta_b)\circ\kappa$.

## Sources

- New: direct from the definitions, in the conventions of [Duality map of a cycle](../../base/complexes/cycle-chain-map.md).

## Depends on

- [Duality pairings](duality-pairing.md)
- [External product of structures](external-product.md)
- [Dual of a tensor product](product-dual-iso.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)
- [Tensor product of complexes](complex-product.md)
- [Dual complexes have finitely many nonzero chain objects](bookkeeping/dual-complex-finite.md)
- [Tensor product of chain maps](bookkeeping/product-map.md)

## Proof depends on

- [External product of structures](external-product.md)
- [Dual of a tensor product](product-dual-iso.md)
- [Support of a tensor product of complexes](bookkeeping/product-support.md)
- [Summand projections of a tensor product](bookkeeping/summand-projection.md)
- [Summands outside the support vanish](bookkeeping/summand-zero.md)
- [Maps into a tensor product are determined by their components](bookkeeping/product-hom-ext.md)
- [Maps out of the dual of a tensor product are determined by their components](bookkeeping/product-dual-hom-ext.md)
