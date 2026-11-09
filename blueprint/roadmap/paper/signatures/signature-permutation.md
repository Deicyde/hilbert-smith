---
declaration: lemma
origin: bridged
---

# Permutation rule on $L^p_4$

$\mathrm{Sign}_G((\tau_X)_*x)(g)=|X^g|\,\mathrm{Sign}_G(x)(g)$.

*Proof sketch.* Choose a representative $(C,\varphi)$. Then $(\tau_X)_*[C,\varphi]=[\tau_XC,1\otimes\varphi]$ ([induced map](../l-theory/base/induced-map.md)). Apply [the middle form of a permutation tensor](middle-form-permtensor.md), then [isometry](form-signature-isometry.md), then [the form rule](form-signature-permutation.md).

## Sources

- HS paper, Section 3

## Depends on

- [Permutation tensor](permutation-tensor.md)
- [Signature hom](signature-hom.md)
- [Induced homomorphism](../l-theory/base/induced-map.md)

## Proof depends on

- [Middle form of a permutation tensor](middle-form-permtensor.md)
- [Form permutation rule](form-signature-permutation.md)
