---
article_id: af_5a19ebe2cf0a2be2d9003212
declaration: lemma
origin: background
statement: formalized
lean: HSP.pairMap_prod_line
proof: formalized
---

# The pair map of a product with the line

Let $f:C\to D$ be a chain map in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$, $\phi\in M(C)_m$ a cycle and $\delta\phi\in M(D)_n$, $n=m+1$, with $\partial\delta\phi=f_\%\phi$, and let $\psi:D^{n-*}\to\mathcal C(f)$ be the [pair map](../../base/pairs/pair-map.md). Suppose that $\phi\otimes\lambda$ is a cycle and $\partial(\delta\phi\otimes\lambda)=(f\otimes1)_\%(\phi\otimes\lambda)$, for the [external products](../products/external-product.md) with the [structure of the symmetric line](../products/symmetric-line-structure.md). There is an isomorphism of complexes
$$J:\mathcal C(f)\otimes\Lambda\cong\mathcal C(f\otimes1)$$
from the [product](../products/complex-product.md) of the [mapping cone](../../base/complexes/cone.md) with the line to the cone of the [product](../products/bookkeeping/product-map.md) $f\otimes1$, whose restriction to the summand $\mathcal C(f)_a\boxtimes\Lambda_b=(D_a\oplus C_{a-1})\boxtimes\Lambda_b$ is $\mathrm{pr}_D\boxtimes1$ followed by the inclusion of $D_a\boxtimes\Lambda_b$ into $(D\otimes\Lambda)_{a+b}$, plus $(-1)^b$ times $\mathrm{pr}_C\boxtimes1$ followed by the inclusion of $C_{a-1}\boxtimes\Lambda_b$ into $(C\otimes\Lambda)_{a+b-1}$ ([Summand inclusions of a tensor product](../products/bookkeeping/summand-inclusion.md)). For this $J$, the pair map $\psi^\times$ of $(f\otimes1,\delta\phi\otimes\lambda,\phi\otimes\lambda)$ is
$$\psi^\times=J\circ(\psi\otimes\lambda_\natural)\circ\Xi,$$
with $\Xi:(D\otimes\Lambda)^{n+1-*}\cong D^{n-*}\otimes\Lambda^{1-*}$ the [duality isomorphism of products](../products/product-dual-iso.md).

*Proof sketch.* Write $s(a,b)=(-1)^{b(a+n)}$ for the sign of $\delta\phi\otimes\lambda$ on the block with target $D_a\boxtimes\Lambda_b$.
1. $J$ is a chain map: from $C_{a-1}\boxtimes\Lambda_b$, the component to $D_{a-1}\boxtimes\Lambda_b$ is $(-1)^{a-1}f\boxtimes1$ in the source and $(-1)^{a+b-1}f\boxtimes1$ in the target, and the component to $C_{a-1}\boxtimes\Lambda_{b-1}$ is $(-1)^a1\boxtimes d$ in the source and $(-1)^{a-1}1\boxtimes d$ in the target; the factor $(-1)^b$ reconciles both. On $D_a\boxtimes\Lambda_b$ both differentials agree. Its inverse is given by the same formula with $\mathrm{in}_D$, $\mathrm{in}_C$ in place of the projections.
2. On the summand $D^*_{n-a}\boxtimes\Lambda^*_{1-b}$, both $\psi^\times$ and $J\circ(\psi\otimes\lambda_\natural)\circ\Xi$ have $D$-component $s(a,b)\,\delta\phi_a\boxtimes\lambda_b$ and $C$-component $(-1)^{a+b}s(a,b)\,\phi_{a-1}f^*_{n-a}\boxtimes\lambda_b$. For $\psi^\times$ this uses that the sign of the $m$-dimensional $\phi\otimes\lambda$ at target $C_{a-1}\boxtimes\Lambda_b$ is $(-1)^{b(a-1+m)}=s(a,b)$.

## Sources

- [Ranicki 1980 I, §8, products of pairs](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign computation in this paper's conventions, split out of the product of a pair with the line.

## Depends on

- [Pair map](../../base/pairs/pair-map.md)
- [Mapping cone](../../base/complexes/cone.md)
- [Tensor product of complexes](../products/complex-product.md)
- [Tensor product of chain maps](../products/bookkeeping/product-map.md)
- [Summand inclusions of a tensor product](../products/bookkeeping/summand-inclusion.md)
- [External product of structures](../products/external-product.md)
- [Structure of the symmetric line](../products/symmetric-line-structure.md)
- [Dual of a tensor product](../products/product-dual-iso.md)
- [Box product on iterated bounded categories](../products/box-pairing-pow.md)

## Proof depends on

- [Duality pairings](../products/duality-pairing.md)
- [The sums in a tensor product of complexes exist](../products/bookkeeping/product-sums-exist.md)
- [Summand projections of a tensor product](../products/bookkeeping/summand-projection.md)
- [Projection after inclusion of the same summand](../products/bookkeeping/inclusion-projection.md)
- [Projection after inclusion of another summand](../products/bookkeeping/inclusion-projection-ne.md)
- [Maps into a tensor product are determined by their components](../products/bookkeeping/product-hom-ext.md)
- [Maps out of the dual of a tensor product are determined by their components](../products/bookkeeping/product-dual-hom-ext.md)
- [Support of a tensor product of complexes](../products/bookkeeping/product-support.md)
- [Summands outside the support vanish](../products/bookkeeping/summand-zero.md)
- [Differential of a tensor product on summands](../products/bookkeeping/product-differential.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)
