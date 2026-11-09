---
article_id: af_f3183d8d69a234085e0779b4
declaration: lemma
origin: bridged
---

# Permutation rule on $L^p_4$

$\mathrm{Sign}_G((\tau_X)_*x)(g)=|X^g|\,\mathrm{Sign}_G(x)(g)$.

*Proof sketch.* Choose a representative $(C,\varphi)$. Then $(\tau_X)_*[C,\varphi]=[\tau_XC,1\otimes\varphi]$ ([induced map](../../l-theory/base/groups/induced-map.md)). Apply [the middle form of a permutation tensor](middle-form-permtensor.md), then [isometry](../forms/form-signature-isometry.md), then [the form rule](../forms/form-signature-permutation.md).

## Sources

- HS paper, Section 3

## Depends on

- [Permutation tensor](../point-functors/permutation-tensor.md)
- [Signature hom](signature-hom.md)
- [Induced homomorphism](../../l-theory/base/groups/induced-map.md)

## Proof depends on

- [Middle form of a permutation tensor](middle-form-permtensor.md)
- [Form permutation rule](../forms/form-signature-permutation.md)
