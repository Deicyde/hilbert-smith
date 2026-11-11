---
article_id: af_1e5f22ca0bfce71faf56f104
declaration: def
origin: bridged
statement: formalized
lean: HSP.UPair.image
---

# Image of a pair with boundary in Kar U

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](../decorations/decorated-object.md), and let $V=(f:iP\to D,\delta\phi,i_\%\pi)$ be a strict $k$-dimensional [$\mathcal U$-pair](u-pair.md). Its *image* is
$$qV=(qD,\ q_\%\delta\phi),$$
a strict $k$-dimensional symmetric Poincaré complex in $\mathrm{Dec}(\mathcal A/\mathcal U)$. Write $[qV]$ for its class in $L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$.

*Proof sketch.* (The image is a strict Poincaré complex with decorated chain objects.) (1) $q\circ i$ sends every object to a zero object: for $(V,e)$ with $V\in\mathcal U$, the idempotent $e$ factors through $V$, so $[e]=0$ in $\mathcal A/\mathcal U$. Hence every map into or out of $qiP_r$ is zero, and in particular $qf=0$. (2) $qD_r$ vanishes outside $[0,k]$, $T(q_\%\delta\phi)=q_\%T\delta\phi=q_\%\delta\phi$, and $\partial(q_\%\delta\phi)=q_\%(f_\%i_\%\pi)=(qf)_\%(q_\%i_\%\pi)=0$. (3) In $\mathcal C(qf)_r=qD_r\oplus qiP_{r-1}$ the second summand is a zero object and $qf=0$, so the projection $\mathcal C(qf)\to qD$ is an isomorphism of complexes. Composed with $q$ of the [pair map](../../base/pairs/pair-map.md) $\psi_r=(\delta\phi_r,(-1)^r\pi_{r-1}f^*)$ it gives $(q_\%\delta\phi)_\natural$. Since $q\psi$ is a chain homotopy equivalence, so is $(q_\%\delta\phi)_\natural$. (4) $[qD_r]$ is the class of an image, so $qD_r$ is decorated.

## Sources

- New: direct from the definitions; the HS paper uses this image in Section 6 (lines 565-568)

## Depends on

- [U-pairs](u-pair.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Decorated quotient L-group](../decorations/decorated-l-group.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Complexes in a full subcategory](../decorations/complex-in-subcategory.md)

## Proof depends on

- [Pair map](../../base/pairs/pair-map.md)
- [Pushforward commutes with T](../../base/complexes/structure-push-involution.md)
