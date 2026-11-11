---
article_id: af_0d523d9709ac6cef82bded0d
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.d_π
proof: formalized
---

# Differential of a tensor product on summands

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. For $p+q=r-1$, the differential $d:(C\otimes E)_r\to(C\otimes E)_{r-1}$ of the [tensor product](../complex-product.md) satisfies
$$\pi_{p,q}\,d=(d\boxtimes1)\,\pi_{p+1,q}+(-1)^p(1\boxtimes d)\,\pi_{p,q+1},$$
for the [summand projections](summand-projection.md).

*Proof sketch.* Maps out of $(C\otimes E)_r$ are determined on the summands $C_a\boxtimes E_b$, $a+b=r$. There $d\,\iota_{a,b}=\iota_{a-1,b}(d\boxtimes1)+(-1)^a\iota_{a,b-1}(1\boxtimes d)$ by the definition of the differential. Composing with $\pi_{p,q}$, [Projection after inclusion of the same summand](inclusion-projection.md) and [of another summand](inclusion-projection-ne.md) leave $d\boxtimes1$ exactly when $(a,b)=(p+1,q)$, $(-1)^p\,1\boxtimes d$ exactly when $(a,b)=(p,q+1)$, and $0$ otherwise. The right side gives the same, by the same two lemmas.

## Sources

- New: direct from the definition of the differential.

## Depends on

- [Tensor product of complexes](../complex-product.md)
- [Summand projections of a tensor product](summand-projection.md)

## Proof depends on

- [Summand inclusions of a tensor product](summand-inclusion.md)
- [Projection after inclusion of the same summand](inclusion-projection.md)
- [Projection after inclusion of another summand](inclusion-projection-ne.md)
