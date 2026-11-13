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
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Dual complex](../../base/complexes/dual-complex.md)
- [Structure complex](../../base/complexes/structure-complex.md)

## Proof depends on

- [Support of a tensor product of complexes](bookkeeping/product-support.md)
- [Summand projections of a tensor product](bookkeeping/summand-projection.md)
- [Projection after inclusion of the same summand](bookkeeping/inclusion-projection.md)
- [Projection after inclusion of another summand](bookkeeping/inclusion-projection-ne.md)
- [Summands outside the support vanish](bookkeeping/summand-zero.md)
- [Maps into a tensor product are determined by their components](bookkeeping/product-hom-ext.md)
- [Maps out of the dual of a tensor product are determined by their components](bookkeeping/product-dual-hom-ext.md)
- [A duality pairing is additive in the first variable](bookkeeping/pairing-additive-left.md)
- [A duality pairing is additive in the second variable](bookkeeping/pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](bookkeeping/product-sums-exist.md)
- [Summand inclusions of a tensor product](bookkeeping/summand-inclusion.md)
- [Signs for tensor products of chain complexes](bookkeeping/tensor-signs.md)
