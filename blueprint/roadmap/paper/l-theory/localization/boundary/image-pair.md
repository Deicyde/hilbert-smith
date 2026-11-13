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
a strict $k$-dimensional symmetric Poincaré complex in $\mathrm{Dec}(\mathcal A/\mathcal U)$. Write $[qV]$ for its class in $L_k(\mathrm{Dec}(\mathcal A/\mathcal U))=L^{\mathrm{im}}_k(\mathcal A/\mathcal U)$, the decorated quotient L-group.

*Proof sketch.* (The image is a strict Poincaré complex with decorated chain objects.) (1) $q\circ i$ sends every object to a zero object: for $(V,e)$ with $V\in\mathcal U$, the idempotent $e$ factors through $V$, so $[e]=0$ in $\mathcal A/\mathcal U$. Hence every map into or out of $qiP_r$ is zero, and in particular $qf=0$. (2) $qD_r$ vanishes outside $[0,k]$, $T(q_\%\delta\phi)=q_\%T\delta\phi=q_\%\delta\phi$, and $\partial(q_\%\delta\phi)=q_\%(f_\%i_\%\pi)=(qf)_\%(q_\%i_\%\pi)=0$. (3) The image $q\,\mathcal C(f)$ of the [mapping cone](../../base/complexes/cone.md) has chain objects $q(D_r\oplus iP_{r-1})$, and $q(iP_{r-1})$ is a zero object, so the projection $q\,\mathcal C(f)\to qD$ is an isomorphism of complexes. The [pair map](../../base/pairs/pair-map.md) $\psi_r=(\delta\phi_r,(-1)^r\pi_{r-1}f^*):D^{k-*}\to\mathcal C(f)$ is a chain homotopy equivalence, hence so is $q\psi$. Preceded by the identification of $(qD)^{k-*}$ with $q(D^{k-*})$ ([duality functors and dual complexes](../../base/complexes/functors/functor-dual-iso.md)) and followed by the projection, $q\psi$ gives $(q_\%\delta\phi)_\natural$, which is therefore a chain homotopy equivalence. (4) $[qD_r]$ is the class of an image, so $qD_r$ is decorated.

## Sources

- New: direct from the definitions; the HS paper uses this image in Section 6 (lines 565-568)

## Depends on

- [U-pairs](u-pair.md)
- [Decorated objects](../decorations/decorated-object.md)
- [Strict symmetric Poincaré complex](../../base/pairs/symmetric-poincare-complex.md)
- [Additive subcategory closed under duality](../../base/categories/dual-additive-subcategory.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Duality category of a dual-closed subcategory](../../base/categories/dual-subcategory.md)
- [Quotient by a subcategory](../../base/categories/filtration-quotient.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Decorated objects are closed under sums and duals](../decorations/decorated-closure.md)
- [Decorated objects of the completed quotient](../decorations/decorated-predicate.md)

## Proof depends on

- [Complexes in a full subcategory](../decorations/complex-in-subcategory.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Inclusion of a dual-closed subcategory](../../base/categories/subcategory-inclusion.md)
- [The quotient duality functor](../../base/categories/quotient-duality-functor.md)
- [Pair map](../../base/pairs/pair-map.md)
- [Mapping cone](../../base/complexes/cone.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Image of a complex under a duality functor](../../base/complexes/functors/functor-complex.md)
- [Image of structures under a duality functor](../../base/complexes/functors/functor-structure.md)
- [Images of structures commute with the boundary, T and the duality map](../../base/complexes/functors/functor-structure-laws.md)
- [Duality functors and dual complexes](../../base/complexes/functors/functor-dual-iso.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Maps factoring through a subcategory](../../base/categories/filtration-ideal.md)
- [A duality category has binary direct sums](../../base/categories/sums/dual-binary-biproducts.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)
- [Dual complex](../../base/complexes/dual-complex.md)
- [The involution T](../../base/complexes/structure-involution.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [The class of an object in $K_0$](../../bounded/categories/classes/k-zero-class.md)
- [$K_0$ of an idempotent completion](../../bounded/categories/k-zero.md)
