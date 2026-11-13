---
article_id: af_7ba3d150a160ce1b88a1b2b0
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.total
proof: formalized
---

# A tensor product is the sum of its summands

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. For every $r\in\mathbb Z$,
$$\sum_{(p,q)}\iota_{p,q}\pi_{p,q}=1\quad\text{on }(C\otimes E)_r,$$
the sum running over the [support](product-support.md) of degree $r$, for the [summand inclusions](summand-inclusion.md) and [summand projections](summand-projection.md).

*Proof sketch.* Maps out of the direct sum are determined on the summands $C_p\boxtimes E_q$, $p+q=r$. On a summand in the support, $\pi_{p,q}\iota_{p,q}=1$ ([Projection after inclusion of the same summand](inclusion-projection.md)) and the other terms vanish ([Projection after inclusion of another summand](inclusion-projection-ne.md)). A summand outside the support is a zero object ([Summands outside the support vanish](summand-zero.md)).

## Sources

- New: direct from the definitions.

## Depends on

- [Support of a tensor product of complexes](product-support.md)
- [Summand inclusions of a tensor product](summand-inclusion.md)
- [Summand projections of a tensor product](summand-projection.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)
- [Tensor product of complexes](../complex-product.md)
- [Duality pairings](../duality-pairing.md)

## Proof depends on

- [Projection after inclusion of the same summand](inclusion-projection.md)
- [Projection after inclusion of another summand](inclusion-projection-ne.md)
- [Summands outside the support vanish](summand-zero.md)
- [A duality pairing is additive in the first variable](pairing-additive-left.md)
- [A duality pairing is additive in the second variable](pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](product-sums-exist.md)
- [Signs for tensor products of chain complexes](tensor-signs.md)
