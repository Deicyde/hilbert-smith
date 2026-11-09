---
declaration: def
origin: bridged
---

# The middle form

Let $(C,\varphi)$ be a strict 4-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$. Its component $\varphi_2:C_2^*\to C_2$ maps real 2-cochains to real 2-chains. For classes of cocycles $x,y\in H^2(C;\mathbb R)$ set $b_C([x],[y])=\langle x,\varphi_2y\rangle$, and let $G$ act on $H^2(C;\mathbb R)$ by permutation.

*Proof sketch.* (Well-definedness.) The cycle condition $\partial\varphi=0$ in degree 2 reads $d\varphi_3+\varphi_2d^*=0$. So $\varphi_2$ sends a coboundary to a boundary, and a cocycle to a cycle. A boundary pairs to zero with a cocycle, because $\langle x,dw\rangle=\langle d^Tx,w\rangle$.

## Sources

- HS paper, Section 3
- [published: Ranicki 1980 Part I, §1] [U]

## Depends on

- [Strict symmetric Poincaré complex](../l-theory/base/symmetric-poincare-complex.md)
- [Real chains and cochains](real-homology.md)
