---
article_id: af_0d6db8f1e32d2d6e095a6640
declaration: def
origin: bridged
statement: formalized
lean: HSP.sign
---

# The equivariant signature on $L^p_4$

$\mathrm{Sign}_G:L^p_4(\mathrm{Free}(\mathbb Q[G]))\to(G\to\mathbb R)$, $[C,\varphi]\mapsto\mathrm{Sign}_G(C,\varphi)$, is a well-defined additive homomorphism.

*Proof sketch.* $L^p_4$ is the quotient by cobordism. If $(C,\varphi)$ and $(C',\varphi')$ are cobordant, then $(C\oplus C',\varphi\oplus(-\varphi'))$ is a boundary, and [boundary](boundary-signature-zero.md) gives signature zero. By [middle-form sum](middle-form-sum.md), [middle-form negation](middle-form-neg.md) and [isometry](../forms/form-signature-isometry.md), that signature is $\mathrm{Sign}_G(C)+\mathrm{sign}_{-b_{C'}}$. By [sum](../forms/form-signature-sum.md), which applies because the middle forms are [nonsingular, symmetric and invariant](middle-form-nonsingular.md), and [negation](../forms/form-signature-neg.md) this is $\mathrm{Sign}_G(C)-\mathrm{Sign}_G(C')$. Additivity uses the same two middle-form lemmas, because the sum in $L^p_4$ is $\oplus$.

## Sources

- HS paper, Section 3
- New: defined directly on cobordism classes.

## Depends on

- [Projective L-group](../../l-theory/base/groups/l-group.md)
- [Group structure on L](../../l-theory/base/groups/l-group-add.md)
- [Complex signature](complex-signature.md)

## Proof depends on

- [Cobordism](../../l-theory/base/pairs/cobordism.md)
- [Boundaries have zero signature](boundary-signature-zero.md)
- [Middle form of a sum](middle-form-sum.md)
- [Middle form of the negative](middle-form-neg.md)
- [Middle form nonsingular](middle-form-nonsingular.md)
- [The sum of two Poincaré complexes](../../l-theory/base/pairs/poincare-sum.md)
- [Negative of a Poincaré complex](../../l-theory/base/pairs/poincare-neg.md)
- [Isometry invariance](../forms/form-signature-isometry.md)
- [Additivity](../forms/form-signature-sum.md)
- [Negation](../forms/form-signature-neg.md)
