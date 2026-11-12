---
article_id: af_b5291866e88a5278a2f9ec93
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_T
---

# Products of structures commute with T

For $\varphi\in M(C)_m$ and $\theta\in M(E)_{m'}$ ($E$ vanishing in negative degrees), the [product of structures](based-str-prod.md) commutes with [the involution $T$](../../../../l-theory/base/complexes/structure-involution.md): $T(\varphi\otimes\theta)=T\varphi\otimes T\theta$.

*Proof sketch.* Compare blocks ([maps are determined by their blocks](../blocks/block-ext.md)). The block of $T(\varphi\otimes\theta)_{r,s}=(-1)^{rs}((\varphi\otimes\theta)_{s,r})^*$ is $(-1)^{rs}$ times the transpose of a block of $(\varphi\otimes\theta)_{s,r}$ ([blocks of a transpose](block-dual.md)), computed by the [blocks of a product of structures](str-prod-blocks.md); the transpose of a Kronecker product is the Kronecker product of the transposes ([transpose of a Kronecker product](../kron-dual.md)), and signs come out of the factors ([signs in a Kronecker product](../kron-smul-left.md), [second factor](../kron-smul-right.md)). With $a=m-p$ and $s=k-r$ the signs agree, because $rs+(s-a)(a+m)-(r-p)(p+m)-p(m-p)-(r-p)(m'-r+p)=2(mm'-mr+mp-rp+p^2)$.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [The involution T](../../../../l-theory/base/complexes/structure-involution.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](../blocks/block-ext.md)
- [Blocks of a transpose](block-dual.md)
- [Blocks of a product of structures](str-prod-blocks.md)
- [Transpose of a Kronecker product](../kron-dual.md)
- [Signs in the first factor of a Kronecker product](../kron-smul-left.md)
- [Signs in the second factor of a Kronecker product](../kron-smul-right.md)
