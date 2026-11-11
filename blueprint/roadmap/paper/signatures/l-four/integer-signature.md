---
article_id: af_39ac8d754db288c5e0cb440c
declaration: def
origin: bridged
---

# Integer signature

$\sigma_G:L^p_4(\mathrm{Free}(\mathbb Q[G]))\to\mathbb Z$ is the map $[C,\varphi]\mapsto\dim V^+-\dim V^-$, for an invariant signature splitting $V^+\oplus V^-$ of the [middle form](middle-form.md) $b_C$. It is well defined and additive.

*Proof sketch.* By [the identity value](../forms/form-signature-identity.md), $\dim V^+-\dim V^-=\mathrm{sign}_{b_C}(1)=\mathrm{Sign}_G(C,\varphi)(1)$ ([signature of a complex](complex-signature.md)), so it does not depend on the splitting. [The equivariant signature on $L^p_4$](signature-hom.md) is a well-defined additive homomorphism, so the real number $\mathrm{Sign}_G(C,\varphi)(1)$ depends only on the class $[C,\varphi]$ and is additive in it. Since $\mathbb Z\to\mathbb R$ is injective, the integer is well defined on classes and additive.

**Remark (not formalized).** The value at the identity as a statement about classes is [the integer signature is the value at the identity](integer-signature-identity.md).

## Sources

- HS paper, Section 3

## Depends on

- [The middle form](middle-form.md)
- [Invariant signature splittings exist](signature-splitting-exists.md)

## Proof depends on

- [Identity value](../forms/form-signature-identity.md)
- [Signature of a complex](complex-signature.md)
- [Signature hom](signature-hom.md)
