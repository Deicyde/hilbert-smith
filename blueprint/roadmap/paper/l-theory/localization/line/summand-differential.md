---
article_id: af_62c2a54f904a6e1d68c173b6
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.ι_d
proof: formalized
---

# Differential of a tensor product on a summand

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../products/duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. For $p+q=r$ and every integer $r'$, the component $d:(C\otimes E)_r\to(C\otimes E)_{r'}$ of the differential of the [tensor product](../products/complex-product.md) satisfies, on the [summand](../products/bookkeeping/summand-inclusion.md) $C_p\boxtimes E_q$,
$$d\,\iota_{p,q}=\iota_{p-1,q}\,(d\boxtimes1)+(-1)^p\,\iota_{p,q-1}\,(1\boxtimes d),$$
where the inclusions on the right map into degree $r'$, so both sides are zero unless $r'=r-1$.

*Proof sketch.* This is the definition of the differential of $C\otimes E$ as a total complex, with the signs $1$ and $(-1)^p$ of Signs for tensor products of chain complexes.

## Sources

- New: direct from the definition of the differential.

## Depends on

- [Duality pairings](../products/duality-pairing.md)
- [Tensor product of complexes](../products/complex-product.md)
- [Summand inclusions of a tensor product](../products/bookkeeping/summand-inclusion.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [The sums in a tensor product of complexes exist](../products/bookkeeping/product-sums-exist.md)
