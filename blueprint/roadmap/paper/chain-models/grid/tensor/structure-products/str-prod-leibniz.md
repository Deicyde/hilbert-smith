---
article_id: af_38cee4ab077e5fab8541ebd2
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedStrProd_d
---

# Leibniz rule for products of structures

For $\varphi\in M(C)_m$ and $\theta\in M(E)_{m'}$ ($E$ vanishing in negative degrees), the boundary of the [structure complex](../../../../l-theory/base/complexes/structure-complex.md) of $C\otimes E$ satisfies, for the [product of structures](based-str-prod.md),
$$\partial(\varphi\otimes\theta)=\partial\varphi\otimes\theta+(-1)^m\varphi\otimes\partial\theta.$$

*Proof sketch.* Compare blocks ([maps are determined by their blocks](../block-ext.md)) from the dual of the summand $a$ of degree $s$ to the summand $p$ of degree $r$. In $(\partial F)_{r,s}=dF_{r+1,s}+(-1)^rF_{r,s+1}d^*$ expand the composites through the intermediate summands ([blocks of a composite](../block-comp.md)), using the [blocks of a product of structures](str-prod-blocks.md), the blocks $d\boxtimes1$ and $(-1)^p1\boxtimes d$ of the differential ([block extraction](../block-extraction.md)) and their transposes ([blocks of a transpose](block-dual.md), [transpose of a Kronecker product](../kron-dual.md)). If $a=m-1-p$, only the paths through $C_{p+1}\boxtimes E_{r-p}$ and through the dual of $C_{a+1}\boxtimes E_{s-a}$ survive; with the [Kronecker product of composites](../kron-composite.md) they give the two terms $d\varphi_{p+1}$ and $(-1)^p\varphi_pd^*$ of $(\partial\varphi)_p$ in $\partial\varphi\otimes\theta$, with signs $(r-p)(p+1+m)\equiv(r-p)(p+m-1)$ and $r+(r-p)(p+m)\equiv(r-p)(p+m-1)+p$. If $a=m-p$, only the paths through $C_p\boxtimes E_{r+1-p}$ and the dual of $C_a\boxtimes E_{s+1-a}$ survive, giving the two terms of $(-1)^m\varphi_p\boxtimes(\partial\theta)_{r-p}$ ([additivity](../kron-add-right.md), [signs](../kron-smul-right.md)). Otherwise every path vanishes. Summands of negative degree have dimension zero.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Product of structures in explicit bases](based-str-prod.md)
- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)

## Proof depends on

- [Maps between concatenations are determined by their blocks](../block-ext.md)
- [Blocks of a composite](../block-comp.md)
- [Block extraction](../block-extraction.md)
- [Blocks of a product of structures](str-prod-blocks.md)
- [Blocks of a transpose](block-dual.md)
- [Transpose of a Kronecker product](../kron-dual.md)
- [Kronecker product of composites](../kron-composite.md)
- [Additivity of the Kronecker product in the first factor](../kron-add-left.md)
- [Additivity of the Kronecker product in the second factor](../kron-add-right.md)
- [Signs in the first factor of a Kronecker product](../kron-smul-left.md)
- [Signs in the second factor of a Kronecker product](../kron-smul-right.md)
