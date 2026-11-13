---
article_id: af_8194e6b68b0cc41318814187
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.dual_hom_ext
proof: formalized
---

# Maps out of the dual of a tensor product are determined by their components

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. Two maps $f,g:((C\otimes E)_r)^*\to Z$ with $f\pi_{p,q}^*=g\pi_{p,q}^*$ for all $p+q=r$ are equal, for the [summand projections](summand-projection.md).

*Proof sketch.* Dualizing [A tensor product is the sum of its summands](product-total.md) gives $\sum\pi_{p,q}^*\iota_{p,q}^*=1$ on $((C\otimes E)_r)^*$, since the duality is additive and contravariant. Hence $f=\sum f\pi_{p,q}^*\iota_{p,q}^*=\sum g\pi_{p,q}^*\iota_{p,q}^*=g$.

## Sources

- New: direct from the definitions.

## Depends on

- [Summand projections of a tensor product](summand-projection.md)
- [Duality category](../../../base/categories/duality-category.md)
- [Tensor product of complexes](../complex-product.md)
- [Duality pairings](../duality-pairing.md)

## Proof depends on

- [A tensor product is the sum of its summands](product-total.md)
- [Summand inclusions of a tensor product](summand-inclusion.md)
- [Support of a tensor product of complexes](product-support.md)
