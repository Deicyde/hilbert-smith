---
article_id: af_f43570e8796a48f1d3a478bd
declaration: def
origin: bridged
---

# Induced homomorphism

A duality functor $(F,\xi):\mathcal A\to\mathcal B$ induces a homomorphism $F_*:L^p_k(\mathcal A)\to L^p_k(\mathcal B)$, $[C,\phi]\mapsto[FC,F_\%\phi]$, computed through [Completion of a duality functor](../categories/karoubi-functor.md), with $(F_\%\phi)_r=F(\phi_r)\circ\xi^{-1}_{C_{k-r}}$.

*Proof sketch.* (1) $F_\%$ commutes with $\partial$, and with $T$ because $\xi_M^*=\xi_{M^*}$. $F$ is additive, so it carries zero objects to zero objects and the support conditions are kept. (2) $(F_\%\phi)_\natural$ is $F(\phi_\natural)$ composed with the isomorphism $\xi:(FC)^{k-*}\cong F(C^{k-*})$, so Poincaré complexes go to Poincaré complexes. Likewise the image of a pair map is $F(\psi)$ composed with $\xi$ and $F(\mathcal C(f))\cong\mathcal C(Ff)$, so pairs go to pairs. A cobordism goes to a pair with boundary $(F(C\oplus C'),F_\%(\phi\oplus(-\phi')))$. The canonical isomorphism $u:FC\oplus FC'\cong F(C\oplus C')$ carries $F_\%\phi\oplus(-F_\%\phi')$ to that structure, so [Transport of pairs along isomorphisms](../pairs/pair-transport.md) ($s=1$) makes it a cobordism. (3) $[F(C\oplus C')]=[FC\oplus FC']$ by [Homotopy-isometry invariance](homotopy-isometry-invariance.md) with $h=u^{-1}$ and $\chi=0$, so $F_*$ is additive.

## Sources

- New: direct from the definitions

## Depends on

- [Group structure on L^p](l-group-add.md)
- [Completion of a duality functor](../categories/karoubi-functor.md)

## Proof depends on

- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Homotopy-isometry invariance](homotopy-isometry-invariance.md)
