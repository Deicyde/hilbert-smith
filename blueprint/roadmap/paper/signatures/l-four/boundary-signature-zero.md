---
article_id: af_8c976a2c7ac1ef9ed35da931
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.complexSign_boundary
---

# Boundaries have zero signature

If $(C,\varphi)$ is the boundary of a strict 5-dimensional symmetric Poincaré pair in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$, then $\mathrm{Sign}_G(C,\varphi)=0$.

*Proof sketch.* [The pair Lagrangian](pair-lagrangian.md) gives an invariant isotropic $L$ of half dimension. Apply [the Lagrangian lemma](../forms/form-signature-lagrangian.md).

## Sources

- HS paper, Section 3
- New: the Lagrangian is produced directly, with no Witt-group identification.

## Depends on

- [Strict Poincaré pair](../../l-theory/base/pairs/poincare-pair.md)
- [Complex signature](complex-signature.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)

## Proof depends on

- [Pair Lagrangian](pair-lagrangian.md)
- [Invariant Lagrangians](../forms/form-signature-lagrangian.md)
