---
article_id: af_6198be95a462226317ed1ab0
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedComplexTensor_dim_neg
---

# The tensor product vanishes in negative degrees

Let $C$ and $E$ be complexes of based vector spaces with $E_q=0$ for $q<0$. Then the [tensor product](../based-complex-tensor.md) $C\otimes E$ also vanishes in negative degrees: $(C\otimes E)_r=0$ for $r<0$.

*Proof sketch.* The only summand of degree $r<0$ is $C_0\boxtimes E_r$, and $E_r=0$.

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [The category of based ℚ-vector spaces](../../../l-theory/localization/products/bookkeeping/based-category.md)
