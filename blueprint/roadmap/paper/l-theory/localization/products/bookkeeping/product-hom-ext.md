---
article_id: af_4ec7d78118154c67e57f6831
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.hom_ext_to
proof: formalized
---

# Maps into a tensor product are determined by their components

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. Two maps $f,g:Z\to(C\otimes E)_r$ with $\pi_{p,q}f=\pi_{p,q}g$ for all $p+q=r$ are equal, for the [summand projections](summand-projection.md).

*Proof sketch.* $f=\sum\iota_{p,q}\pi_{p,q}f=\sum\iota_{p,q}\pi_{p,q}g=g$ by [A tensor product is the sum of its summands](product-total.md).

## Sources

- New: direct from the definitions.

## Depends on

- [Summand projections of a tensor product](summand-projection.md)

## Proof depends on

- [A tensor product is the sum of its summands](product-total.md)
