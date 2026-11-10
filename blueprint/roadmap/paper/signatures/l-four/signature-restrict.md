---
article_id: af_a7d89c6402a0d3ac410d355d
declaration: lemma
origin: bridged
---

# Restriction on $L^p_4$

For $H\le G$, $x\in L^p_4(\mathrm{Free}(\mathbb Q[G]))$ and $h\in H$, $\mathrm{Sign}_H((\mathrm{res}^G_H)_*x)(h)=\mathrm{Sign}_G(x)(h)$, where $\mathrm{res}^G_H$ is [restriction to the subgroup](../point-functors/restriction-functor.md).

*Proof sketch.* Choose a representative $x=[C,\varphi]$, so $(\mathrm{res}^G_H)_*x=[\mathrm{res}\,C,\mathrm{res}_\%\varphi]$ ([induced map](../../l-theory/base/groups/induced-map.md)). $\mathrm{res}^G_H$ reindexes every matrix along the $H$-equivariant bijection $(h',(j,k))\mapsto(h'g_j,k)$. Its permutation matrix is orthogonal and carries the real cochains, the coboundary and $\varphi_2$ of $\mathrm{res}\,C$ to those of $C$, so it is an $H$-equivariant isometric isomorphism from $b_{\mathrm{res}\,C}$ to $b_C$ with the action restricted to $H$. Apply [isometry invariance](../forms/form-signature-isometry.md) for $H$ and [the form rule](../forms/form-signature-restrict.md).

## Sources

- HS paper, Section 3 (used in the divisibility step)

## Depends on

- [Restriction to a subgroup](../point-functors/restriction-functor.md)
- [The equivariant signature on $L^p_4$](signature-hom.md)
- [Induced homomorphism](../../l-theory/base/groups/induced-map.md)

## Proof depends on

- [Isometry invariance](../forms/form-signature-isometry.md)
- [Restriction of the form signature](../forms/form-signature-restrict.md)
