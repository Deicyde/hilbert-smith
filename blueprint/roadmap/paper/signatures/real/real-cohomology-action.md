---
article_id: af_826dc8ef23f37368c3e03db8
declaration: def
origin: background
statement: formalized
lean: HSP.realHco.rep
---

# The action of the group on real cohomology

$G$ acts on $\mathbb R^{G\times\{1..n\}}$ by permuting the basis, $a(g,k)=(a+g,k)$ in the additive notation of the [free category](../../categories/asymptotic/free-category.md), that is $(a\cdot v)(g,k)=v(-a+g,k)$. Equivariant [real matrices](real-matrix.md) commute with this action, so it preserves the real cocycles and coboundaries of a chain complex $C$ in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ and induces a representation of $G$ on the [real cohomology](real-cohomology.md) $H^r(C;\mathbb R)$.

*Proof sketch.* (Well-definedness.) For an equivariant matrix $u$, $(u(a\cdot v))(g,k')=\sum_{h,k}u_{(g,k'),(h,k)}v(-a+h,k)=\sum_{h,k}u_{(-a+g,k'),(h,k)}v(h,k)=(a\cdot uv)(g,k')$, by reindexing $h\mapsto a+h$ and equivariance. So the action commutes with $e_r^T$ and with $d^T$.

## Sources

- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Real cohomology](real-cohomology.md)
- [The real matrix of a morphism](real-matrix.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
