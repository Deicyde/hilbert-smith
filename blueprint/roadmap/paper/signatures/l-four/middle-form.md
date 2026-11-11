---
article_id: af_83020c119e44c59c798dd314
declaration: def
origin: bridged
statement: formalized
lean: HSP.middleForm
---

# The middle form

Let $(C,\varphi)$ be a strict 4-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$. Its component $\varphi_2:C_2^*\to C_2$ maps real 2-cochains to real 2-chains. The middle form is the bilinear form $b_C([x],[y])=\langle[x],[\varphi_2y]\rangle$ on $H^2(C;\mathbb R)$, for cocycles $x,y$, with the [evaluation pairing](real-evaluation.md); $G$ acts on $H^2(C;\mathbb R)$ by permuting the basis.

*Proof sketch.* (Well-definedness.) The cycle condition $\partial\varphi=0$ in degree 1 reads $d\varphi_2-\varphi_1d^*=0$, so $\varphi_2$ sends a cocycle to a cycle. In degree 2 it reads $d\varphi_3+\varphi_2d^*=0$, so $\varphi_2$ sends a coboundary to a boundary, which is zero in homology. So $[y]\mapsto[\varphi_2y]$ is well defined, and the evaluation pairing is well defined on classes.

## Sources

- HS paper, Section 3
- [Ranicki 1980 Part I, §1](../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Real homology](real-homology.md)
- [Real cohomology](../real/real-cohomology.md)
- [The real matrix of a morphism](../real/real-matrix.md)
- [The evaluation pairing](real-evaluation.md)

## Proof depends on

- [Structure complex](../../l-theory/base/complexes/structure-complex.md)
