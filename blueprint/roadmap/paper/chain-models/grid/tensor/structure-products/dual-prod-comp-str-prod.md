---
article_id: af_7fc912e6b04ccdeb271b77aa
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedDualProd_comp_basedStrProd
---

# A product of structures after a product of duality maps

Let $C$ and $E$ be complexes of based vector spaces vanishing in negative degrees, $\varphi\in M(C)_m$, $\theta\in M(E)_{m'}$, and $f_r:C_r\to C^*_{m-r}$, $g_r:E_r\to E^*_{m'-r}$ graded maps, $k=m+m'$. Then the [product of structures](based-str-prod.md) and the [product of duality maps](based-dual-prod.md) satisfy, in each degree $r$,
$$(\varphi\otimes\theta)_{r,k-r}\circ\Xi^{-1}(f\otimes g)_r=\bigl((\varphi f)\otimes(\theta g)\bigr)_r,$$
the [tensor](../based-tensor-hom.md) of the maps $\varphi_{a,m-a}f_a$ and $\theta_{c,m'-c}g_c$ of degree $0$.

*Proof sketch.* Compare blocks from the summand $a$ to the summand $p$ of degree $r$. The only intermediate dual summand is $m-a$, and then $p=a$; the two signs $(-1)^{(r-a)(a+m)}$ cancel, and the Kronecker products combine. If $m-a<0$ then $C_{m-a}=0$, and if $m-a>k-r$ then $E_{m'-r+a}=0$, so both sides vanish. The right side is computed by the [blocks of a transported tensor](tensor-hom-transport-blocks.md).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [Product of duality maps in explicit bases](based-dual-prod.md)
- [Tensor of graded maps of based complexes](../based-tensor-hom.md)
- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Small Q-linear category with strict duality](../../../../l-theory/base/categories/duality-category.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [Based vector spaces](../../../../l-theory/localization/products/based-vector-spaces.md)
- [The category of based ℚ-vector spaces](../../../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](../blocks/block-ext.md)
- [Blocks of a composite](../blocks/block-comp.md)
- [Blocks of a product of structures](str-prod-blocks.md)
- [Blocks of a product of duality maps](dual-prod-blocks.md)
- [Kronecker product of composites](../kron-composite.md)
- [Kronecker product with a zero factor](../kron-zero.md)
- [Composites through a zero space vanish](zero-dim-comp.md)
- [Blocks of a transported tensor of graded maps](tensor-hom-transport-blocks.md)
- [Block inclusions and projections](../blocks/block-maps.md)
- [Kronecker product of matrices](../../../../l-theory/localization/products/bookkeeping/based-kron.md)
