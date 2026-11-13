---
article_id: af_b73ccdcd714c3691304bc0c6
declaration: lemma
origin: background
statement: formalized
lean: HSP.strProd_push
proof: formalized
---

# Pushforward of products

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), $C,C'$ complexes in $\mathcal B$ and $E,E'$ complexes in $\mathcal E$, each with all but finitely many chain objects zero objects, let $\phi\in M(C)_m$ and $\theta\in M(E)_n$, and let $\phi\otimes\theta$ be their [external product](external-product.md), with block signs $s(p,q)=(-1)^{q(p+m)}$. For chain maps $f:C\to C'$ and $g:E\to E'$, $(f\otimes g)_\%(\phi\otimes\theta)=f_\%\phi\otimes g_\%\theta$, with $f\otimes g$ the [tensor product of chain maps](bookkeeping/product-map.md).

*Proof sketch.* $f\otimes g$ is block diagonal with no signs, so on each block both sides are $s(p,q)\,f\phi_pf^*\boxtimes g\theta_qg^*$, using functoriality of $\boxtimes$ and naturality of $\kappa$.

## Sources

- New: direct from the definitions, in the conventions of [Pushforward of structures](../../base/complexes/structure-push.md).

## Depends on

- [Duality pairings](duality-pairing.md)
- [External product of structures](external-product.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Tensor product of complexes](complex-product.md)
- [Tensor product of chain maps](bookkeeping/product-map.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)
- [Structure complex](../../base/complexes/structure-complex.md)

## Proof depends on

- [Summand projections of a tensor product](bookkeeping/summand-projection.md)
- [Projection after inclusion of the same summand](bookkeeping/inclusion-projection.md)
- [Projection after inclusion of another summand](bookkeeping/inclusion-projection-ne.md)
- [Maps into a tensor product are determined by their components](bookkeeping/product-hom-ext.md)
- [Maps out of the dual of a tensor product are determined by their components](bookkeeping/product-dual-hom-ext.md)
- [A duality pairing is additive in the first variable](bookkeeping/pairing-additive-left.md)
- [A duality pairing is additive in the second variable](bookkeeping/pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](bookkeeping/product-sums-exist.md)
- [Summand inclusions of a tensor product](bookkeeping/summand-inclusion.md)
- [Signs for tensor products of chain complexes](bookkeeping/tensor-signs.md)
