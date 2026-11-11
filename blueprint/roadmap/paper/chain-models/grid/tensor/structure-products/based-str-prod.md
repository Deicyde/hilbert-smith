---
article_id: af_190f8b6eaec640dfce182741
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.basedStrProd
---

# Product of structures in explicit bases

Let $C$ and $E$ be complexes of based vector spaces, $E$ vanishing in negative degrees, and let $\varphi\in M(C)_m$, $\theta\in M(E)_{m'}$ be elements of the [structure complexes](../../../../l-theory/base/complexes/structure-complex.md), $k=m+m'$. Their product $\varphi\otimes\theta\in M(C\otimes E)_k$, on the [tensor product of based complexes](../../based-complex-tensor.md), is the element whose block from the dual of the summand $C_{m-p}\boxtimes E_{m'-q}$ (identified with $C_{m-p}^*\boxtimes E_{m'-q}^*$, with no sign) to the summand $C_p\boxtimes E_q$ is $(-1)^{q(p+m)}\varphi_p\boxtimes\theta_q$, all other blocks being zero.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Structure complex](../../../../l-theory/base/complexes/structure-complex.md)
- [Tensor product of based complexes](../../based-complex-tensor.md)
- [Tensor product of based vector spaces](../../../../l-theory/localization/products/based-tensor.md)
