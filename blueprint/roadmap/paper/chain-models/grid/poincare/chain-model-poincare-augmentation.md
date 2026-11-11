---
article_id: af_27967b79f87eea90d5a43f02
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.chainModel_poincare_augmentation
---

# The chain model is Poincaré: the augmentation

For every $i$ and every $\alpha\in D_N^*$, the degree-$0$ part of $D_i^{N-*}$, the structure $\varphi_i$ of [chain-model duality](../chain-model-duality.md) and the [augmentation](chain-model-aug.md) $\varepsilon$ of the [chain model](../chain-model.md) satisfy $\varepsilon\varphi_i(\alpha)=\alpha(z_i)$, where $z_i$ is the fundamental cycle.

*Proof sketch.* For a [product of structures](../tensor/structure-products/based-str-prod.md) $\varphi\otimes\theta$ with $\varphi\in M(C)_m$, $\theta\in M(E)_{m'}$, $k=m+m'$, only the block from the dual of $C_m\boxtimes E_{m'}$ lands in the summand $C_0\boxtimes E_0$ of degree $0$, with sign $+1$ ([blocks of a product of structures](../tensor/structure-products/str-prod-blocks.md)). So if $\varepsilon_C\varphi_{0,m}=z_C^*$ and $\varepsilon_E\theta_{0,m'}=z_E^*$, then $(\varepsilon_C\boxtimes\varepsilon_E)(\varphi\otimes\theta)_{0,k}=(z_C\boxtimes z_E)^*$ on the summand of $z_C\boxtimes z_E$ ([Kronecker product of composites](../tensor/kron-composite.md), [transpose of a Kronecker product](../tensor/kron-dual.md)). Induct over the circle factors: the unit structure and $\varepsilon\varphi^s(e^*)=1$ ([circle duality](../circle-duality.md) (4)) give it for $C(k_i)$, and $\varepsilon_P\varphi_P(e_4^*)=1$ ([cells of CP^2](../cp2-cells.md)) for $D_i$.

## Sources

- New: the explicit chain model of the cubical grid.

## Depends on

- [Chain-model duality](../chain-model-duality.md)
- [The augmentation of the chain model](chain-model-aug.md)
- [Chain model](../chain-model.md)

## Proof depends on

- [Blocks of a product of structures](../tensor/structure-products/str-prod-blocks.md)
- [Kronecker product of composites](../tensor/kron-composite.md)
- [Transpose of a Kronecker product](../tensor/kron-dual.md)
- [Block decomposition of the identity](../tensor/block-decomposition.md)
- [Circle duality](../circle-duality.md)
- [Cells of CP^2](../cp2-cells.md)
- [The cells of CP^2 vanish in negative degrees](../cp2-dim-neg.md)
