---
article_id: af_a29f25bde525270187fc5377
declaration: lemma
origin: cited
statement: formalized
lean: HSP.SymPair.exists_prod_line
---

# Product of a pair with the line

Let $(f:C\to D,\delta\phi,\phi)$ be a strict $k$-dimensional symmetric Poincaré pair in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$. Then
$$(f\otimes1:C\otimes\Lambda\to D\otimes\Lambda,\ \delta\phi\otimes\lambda,\ \phi\otimes\lambda)$$
is a strict $(k+1)$-dimensional symmetric Poincaré pair in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$. Its boundary is $(C\otimes\Lambda,\phi\otimes\lambda)$, with no sign.

*Proof sketch.* Write $s(a,b)=(-1)^{b(a+k)}$ for the sign of $\delta\phi\otimes\lambda$ on the block with target $D_a\boxtimes\Lambda_b$.
1. Degrees. $D\otimes\Lambda$ has zero objects outside degrees $[0,k+1]$ and $C\otimes\Lambda$ outside $[0,k]$.
2. Symmetry. $T(\delta\phi\otimes\lambda)=T\delta\phi\otimes T\lambda=\delta\phi\otimes\lambda$, and likewise for $\phi\otimes\lambda$ ([Products commute with T](product-involution.md)).
3. Boundary equation. By the [Leibniz rule](product-leibniz.md) and [Pushforward of products](product-push.md), $\partial(\delta\phi\otimes\lambda)=\partial\delta\phi\otimes\lambda+(-1)^k\delta\phi\otimes\partial\lambda=f_\%\phi\otimes\lambda=(f\otimes1)_\%(\phi\otimes\lambda)$, since $\partial\lambda=0$. This is where a sign could enter, and none does.
4. The boundary is Poincaré. $(\phi\otimes\lambda)_\natural=(\phi_\natural\otimes\lambda_\natural)\circ\Xi$ ([Duality map of a product](product-duality-map.md)), an equivalence by [Tensor products of equivalences](product-equivalence.md) and [The line is Poincaré](symmetric-line-poincare.md).
5. Cones. Let $J:\mathcal C(f)\otimes\Lambda\to\mathcal C(f\otimes1)$ be the canonical isomorphism on $D_a\boxtimes\Lambda_b$ and $(-1)^b$ times it on $C_{a-1}\boxtimes\Lambda_b$. It is a chain map: from $C_{a-1}\boxtimes\Lambda_b$, the component to $D_{a-1}\boxtimes\Lambda_b$ is $(-1)^{a-1}f\boxtimes1$ in the source and $(-1)^{a+b-1}f\boxtimes1$ in the target, and the component to $C_{a-1}\boxtimes\Lambda_{b-1}$ is $(-1)^a1\boxtimes d$ in the source and $(-1)^{a-1}1\boxtimes d$ in the target; the factor $(-1)^b$ reconciles both.
6. Pair map. Let $\psi$ be the [pair map](../../base/pairs/pair-map.md) of $(f,\delta\phi,\phi)$ and $\psi^\times$ that of the product. On the summand $D^*_{k-a}\boxtimes\Lambda^*_{1-b}$, both $\psi^\times$ and $J\circ(\psi\otimes\lambda_\natural)\circ\Xi$ have $D$-component $s(a,b)\,\delta\phi_a\boxtimes\lambda_b$ and $C$-component $(-1)^{a+b}s(a,b)\,\phi_{a-1}f^*_{k-a}\boxtimes\lambda_b$. For $\psi^\times$ this uses that the sign of the $(k-1)$-dimensional $\phi\otimes\lambda$ at target $C_{a-1}\boxtimes\Lambda_b$ is $(-1)^{b(a+k-2)}=s(a,b)$. So $\psi^\times=J\circ(\psi\otimes\lambda_\natural)\circ\Xi$, an equivalence by [Tensor products of equivalences](product-equivalence.md).

## Sources

- [Ranicki 1980 I, §8, products of pairs](../../../../../sources/paper/ranicki-1980.md) [U]
- [Ranicki 1992, §16-17, products with the line](../../../../../sources/paper/ranicki-1992.md) [U]
- New: the sign computation in this paper's conventions; it shows the boundary carries no sign.

## Depends on

- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Tensor product of complexes](complex-product.md)
- [External product of structures](external-product.md)
- [The line is Poincaré](symmetric-line-poincare.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Duals of box products](box-dual.md)

## Proof depends on

- [Leibniz rule for products](product-leibniz.md)
- [Products commute with T](product-involution.md)
- [Pushforward of products](product-push.md)
- [Duality map of a product](product-duality-map.md)
- [Tensor products of equivalences](product-equivalence.md)
- [The line is Poincaré](symmetric-line-poincare.md)
- [Mapping cone](../../base/complexes/cone.md)
- [Pair map](../../base/pairs/pair-map.md)
