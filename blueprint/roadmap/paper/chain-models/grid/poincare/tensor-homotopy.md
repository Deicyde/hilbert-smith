---
article_id: af_b9ecc019f619dd04e9e3638f
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.ChainModels.basedTensorHom_homotopy
---

# Tensor product of homotopies

Let $C$ and $E$ be complexes of based vector spaces vanishing in negative degrees. Let $f$, $g$ be maps of degree $0$ and $h$, $k$ maps of degree $1$ of $C$ and $E$ with $f-1=dh+hd$ and $g-1=dk+kd$. Then, for the [tensors of graded maps](../tensor/based-tensor-hom.md) on the [tensor product of based complexes](../based-complex-tensor.md), $f\otimes g-1=dH+Hd$ with $H=h\otimes g+1\otimes k$, where $1$ is the [identity of degree zero](../tensor/id-deg0.md).

*Proof sketch.* Write the differential of $C\otimes E$ as $d\otimes1+1\otimes d$ ([differential of a tensor product](../tensor/tensor-differential.md)) and expand $dH+Hd$ with the [composition of tensors](../tensor/based-tensor-hom-comp.md), which carries the sign $(-1)^{|g'||f|}$: $d(h\otimes g)+(h\otimes g)d=(dh+hd)\otimes g+h\otimes(gd-dg)$ and $d(1\otimes k)+(1\otimes k)d=1\otimes(dk+kd)$. Here $gd=dg$, since $(g-1)d=dkd=d(g-1)$. By additivity in each factor ([left](../tensor/tensor-hom-add-left.md), [right](../tensor/tensor-hom-add-right.md)), $dH+Hd=(f-1)\otimes g+1\otimes(g-1)=f\otimes g-1\otimes1$, and $1\otimes1=1$ ([tensor of identities](../tensor/tensor-hom-id.md)).

## Sources

- New: block calculus for the explicit bases of the chain models.

## Depends on

- [Tensor product of based complexes](../based-complex-tensor.md)
- [Tensor of graded maps of based complexes](../tensor/based-tensor-hom.md)
- [The identity as a map of degree zero](../tensor/id-deg0.md)

## Proof depends on

- [Differential of a tensor product](../tensor/tensor-differential.md)
- [Composition of tensors of graded maps](../tensor/based-tensor-hom-comp.md)
- [Additivity of tensors of graded maps in the first factor](../tensor/tensor-hom-add-left.md)
- [Additivity of tensors of graded maps in the second factor](../tensor/tensor-hom-add-right.md)
- [Tensor of identities](../tensor/tensor-hom-id.md)
