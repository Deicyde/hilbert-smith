---
article_id: af_f3183d8d69a234085e0779b4
declaration: lemma
origin: bridged
---

# Permutation rule on $L^p_4$

Let $X$ be a finite $G$-set and $\tau_X$ [tensoring with the permutation module](../point-functors/permutation-tensor.md). For $x\in L^p_4(\mathrm{Free}(\mathbb Q[G]))$ and $g\in G$, $\mathrm{Sign}_G((\tau_X)_*x)(g)=|X^g|\,\mathrm{Sign}_G(x)(g)$.

*Proof sketch.* Choose a representative $x=[C,\varphi]$. Then $(\tau_X)_*x=[\tau_XC,(\tau_X)_\%\varphi]$ ([induced map](../../l-theory/base/groups/induced-map.md)). Apply [the middle form of a permutation tensor](middle-form-permtensor.md), then [isometry invariance](../forms/form-signature-isometry.md), then [the form rule](../forms/form-signature-permutation.md).

## Sources

- HS paper, Section 3

## Depends on

- [Tensoring with a permutation module](../point-functors/permutation-tensor.md)
- [The equivariant signature on $L^p_4$](signature-hom.md)
- [Induced homomorphism](../../l-theory/base/groups/induced-map.md)

## Proof depends on

- [Middle form of a permutation tensor](middle-form-permtensor.md)
- [Isometry invariance](../forms/form-signature-isometry.md)
- [Permutation tensor rule](../forms/form-signature-permutation.md)
