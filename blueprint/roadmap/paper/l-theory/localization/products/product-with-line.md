---
article_id: af_a29f25bde525270187fc5377
declaration: lemma
origin: cited
statement: formalized
lean: HSP.SymPair.exists_prod_line
proof: formalized
---

# Product of a pair with the line

Let $(f:C\to D,\delta\phi,\phi)$ be a strict $k$-dimensional symmetric Poincaré pair in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$. Then
$$(f\otimes1:C\otimes\Lambda\to D\otimes\Lambda,\ \delta\phi\otimes\lambda,\ \phi\otimes\lambda)$$
is a strict $(k+1)$-dimensional symmetric Poincaré pair in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$. Its boundary is $(C\otimes\Lambda,\phi\otimes\lambda)$, with no sign. The complexes $C$, $D$ and $\Lambda$ have only finitely many nonzero chain objects by their degree bounds, so the products are defined.

*Proof sketch.*
1. Degrees. $D\otimes\Lambda$ has zero objects outside degrees $[0,k+1]$ ([Bounds of products with the line](../line/line-product-bounds.md)). The boundary $(C\otimes\Lambda,\phi\otimes\lambda)$ is the [product of the complex $(C,\phi)$ with the line](../transitions/transition-complex.md), a strict $k$-dimensional symmetric Poincaré complex.
2. Symmetry. $T(\delta\phi\otimes\lambda)=T\delta\phi\otimes T\lambda=\delta\phi\otimes\lambda$ ([Products commute with T](product-involution.md)).
3. Boundary equation. By the [Leibniz rule](product-leibniz.md) and [Pushforward of products](product-push.md), $\partial(\delta\phi\otimes\lambda)=\partial\delta\phi\otimes\lambda+(-1)^k\delta\phi\otimes\partial\lambda=f_\%\phi\otimes\lambda=(f\otimes1)_\%(\phi\otimes\lambda)$, since $\partial\lambda=0$. This is where a sign could enter, and none does.
4. Pair map. Let $\psi$ be the pair map of $(f,\delta\phi,\phi)$ and $\psi^\times$ that of the product. By [The pair map of a product with the line](../line/product-line-pair-map.md), $\psi^\times=J\circ(\psi\otimes\lambda_\natural)\circ\Xi$ for an isomorphism $J:\mathcal C(f)\otimes\Lambda\cong\mathcal C(f\otimes1)$ and the [duality isomorphism of products](product-dual-iso.md) $\Xi$. Since $\psi$ and $\lambda_\natural$ are equivalences ([The line is Poincaré](symmetric-line-poincare.md)), so is $\psi\otimes\lambda_\natural$ ([Tensor products of equivalences](product-equivalence.md)), and hence $\psi^\times$.

## Sources

- [Ranicki 1980 I, §8, products of pairs](../../../../../sources/paper/ranicki-1980.md) [U]
- [Ranicki 1992, §16-17, products with the line](../../../../../sources/paper/ranicki-1992.md) [U]
- New: the sign computation in this paper's conventions; it shows the boundary carries no sign.

## Depends on

- [Box product on iterated bounded categories](box-pairing-pow.md)
- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Tensor product of complexes](complex-product.md)
- [External product of structures](external-product.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Structure of the symmetric line](symmetric-line-structure.md)
- [Tensor product of chain maps](bookkeeping/product-map.md)
- [The symmetric line](symmetric-line.md)
- [Small Q-linear category with strict duality](../../base/categories/duality-category.md)

## Proof depends on

- [The line is Poincaré](symmetric-line-poincare.md)
- [Leibniz rule for products](product-leibniz.md)
- [Products commute with T](product-involution.md)
- [Pushforward of products](product-push.md)
- [Tensor products of equivalences](product-equivalence.md)
- [Dual of a tensor product](product-dual-iso.md)
- [Mapping cone](../../base/complexes/cone.md)
- [The symmetric line is a symmetric complex](symmetric-line-cycle.md)
- [Bounds of products with the line](../line/line-product-bounds.md)
- [The pair map of a product with the line](../line/product-line-pair-map.md)
- [Product of a complex with the line](../transitions/transition-complex.md)
- [Bounded complexes have finitely many nonzero chain objects](../../base/complexes/finite-bounded.md)
- [Pushforward preserves identities](../../base/complexes/functors/push-id.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Dual complexes have finitely many nonzero chain objects](bookkeeping/dual-complex-finite.md)
- [Duality pairings](duality-pairing.md)
