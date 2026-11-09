---
declaration: lemma
origin: bridged
---

# The duality square of a pair

Let $(f:C\to D,\delta\varphi,\varphi)$ be a strict 5-dimensional symmetric Poincaré pair in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$. Then, inside $H_2(C;\mathbb R)$,
$$\varphi_2\big(f^*H^2(D;\mathbb R)\big)=\ker\big(f_*:H_2(C;\mathbb R)\to H_2(D;\mathbb R)\big).$$

*Proof sketch.* (1) Exactness of the cone at $H_2(C)$. Let $p:\mathcal C(f)_3=D_3\oplus C_2\to C_2$ be the projection. A pair $(x,y)$ is a cycle of $\mathcal C(f)$ iff $dy=0$ and $dx+fy=0$, and boundaries project to boundaries. Hence $p$ maps $H_3(\mathcal C(f);\mathbb R)$ onto $\ker f_*$. (2) The square. The pair map is $\psi_3=(\delta\varphi_3,-\varphi_2f^*)$ on $D^*_2$. So $p\,\psi_3=-\varphi_2f^*$ on cocycles. (3) $\psi$ is a homotopy equivalence, so every class of $H_3(\mathcal C(f);\mathbb R)$ is $[\psi_3y]$ for some cocycle $y$ of $D$ ([invariance](real-homology-invariance.md)). Combine (1)-(3).

## Sources

- [published: Ranicki 1980 Part I, §3, algebraic Poincaré-Lefschetz duality] [U]
- New: only the one square needed here, done by hand.

## Depends on

- [Strict Poincaré pair](../l-theory/base/poincare-pair.md)
- [Real chains and cochains](real-homology.md)

## Proof depends on

- [Sign conventions](../l-theory/base/conventions.md)
- [Real homology is homotopy invariant](real-homology-invariance.md)
