---
article_id: af_3f3d2a85346656d1ded0e1cc
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_comp_basedTensorHom_comp_basedDualProd
---

# A tensor between a product of structures and a product of duality maps

Let $C$ and $E$ be complexes of based vector spaces vanishing in negative degrees, $m+m'=k$, $\varphi\in M(C)_m$, $\theta\in M(E)_{m'}$, $F$, $G$ graded maps of $C$, $E$ of degrees $d$, $e$, and $f_r:C_r\to C_{m-r}^*$, $g_r:E_r\to E_{m'-r}^*$. Then the [product of duality maps](based-dual-prod.md) after the [tensor](../based-tensor-hom.md) $F\otimes G$ after the [product of structures](based-str-prod.md) is the [dual tensor](../based-dual-tensor-hom.md) of the factorwise composites: $\Xi^{-1}(f\otimes g)(F\otimes G)(\varphi\otimes\theta)\Xi=\Xi^{-1}(fF\varphi\otimes gG\theta)\Xi$, with no sign.

*Proof sketch.* Blockwise ([blocks of a product of structures](str-prod-blocks.md), [blocks of a transported tensor](tensor-hom-transport-blocks.md), [blocks of a product of duality maps](dual-prod-blocks.md), [blocks of a dual tensor](dual-tensor-hom-blocks.md), [composition of block matrices](../blocks/block-comp.md)): from a given summand each factor has at most one nonzero block, and the signs $(-1)^{q(p+m)}$, $(-1)^{ep}$ and $(-1)^{(q+e)(p+d+m)}$ multiply to the sign of the dual tensor. The Kronecker products compose factorwise ([Kronecker product of composites](../kron-composite.md)). Out of range a factor passes through a zero-dimensional space ([a composite through a zero space](zero-dim-comp.md), [Kronecker product with a zero factor](../kron-zero.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [Tensor of graded maps of based complexes](../based-tensor-hom.md)
- [Product of duality maps in explicit bases](based-dual-prod.md)
- [Dual tensor of graded maps of based complexes](../based-dual-tensor-hom.md)

## Proof depends on

- [Blocks of a product of structures](str-prod-blocks.md)
- [Blocks of a transported tensor of graded maps](tensor-hom-transport-blocks.md)
- [Blocks of a product of duality maps](dual-prod-blocks.md)
- [Blocks of a dual tensor of graded maps](dual-tensor-hom-blocks.md)
- [Blocks of a composite](../blocks/block-comp.md)
- [Maps between concatenations are determined by their blocks](../blocks/block-ext.md)
- [Kronecker product of composites](../kron-composite.md)
- [Composites through a zero space vanish](zero-dim-comp.md)
- [Kronecker product with a zero factor](../kron-zero.md)
