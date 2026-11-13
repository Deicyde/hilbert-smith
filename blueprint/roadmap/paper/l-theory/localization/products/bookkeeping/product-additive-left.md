---
article_id: af_07d3e9c183e90e1b53091b00
declaration: lemma
origin: background
statement: formalized
lean: HSP.strProd_add_left
proof: formalized
---

# External products are additive in the first structure

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. For $\phi,\phi'\in M(C)_m$ and $\theta\in M(E)_n$, the [external products](../external-product.md) satisfy
$$(\phi+\phi')\otimes\theta=\phi\otimes\theta+\phi'\otimes\theta.$$

*Proof sketch.* Each block $(-1)^{q(p+m)}\kappa\circ(\phi_p\boxtimes\theta_q)$ is additive in $\phi$, since $\boxtimes$ is additive in the first variable and composition is bilinear.

## Sources

- New: direct from the definition.

## Depends on

- [External product of structures](../external-product.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)
- [Structure complex](../../../base/complexes/structure-complex.md)
- [Tensor product of complexes](../complex-product.md)
- [Duality pairings](../duality-pairing.md)

## Proof depends on

- [Support of a tensor product of complexes](product-support.md)
- [Summand inclusions of a tensor product](summand-inclusion.md)
