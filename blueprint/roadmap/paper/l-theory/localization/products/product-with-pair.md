---
article_id: af_ff039a6fe2db192637b0e08d
declaration: lemma
origin: cited
---

# Product of a complex with a pair over the line

Let $(C,\phi)$ be a strict $m$-dimensional symmetric Poincaré complex in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$, and let $(g:B\to E,\delta\theta,\theta)$ be a strict $n$-dimensional symmetric Poincaré pair whose chain objects lie in $C_\mathbb Z(\mathbb Q)$. Then
$$(1\otimes g:C\otimes B\to C\otimes E,\ \phi\otimes\delta\theta,\ (-1)^m\phi\otimes\theta)$$
is a strict $(m+n)$-dimensional symmetric Poincaré pair in $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$, with boundary $(C\otimes B,(-1)^m\phi\otimes\theta)$.

**Remark (not formalized).** For the ray pair $(f:\mathrm{pt}_0\to\Lambda_+)$ of [The symmetric ray](../../comparison/symmetric-ray.md), whose boundary structure is $\sigma_0=-1$, the boundary of the product is $C$ placed in position $0$ with structure $(-1)^{m+1}\phi$: the blocks of $\phi\otimes1$ on $C\otimes\mathrm{pt}_0$ have sign $(-1)^{0\cdot(a+m)}=1$. So the sign called $\varepsilon_m$ in [The truncated line is a pair](../../comparison/truncated-line-pair.md) is $(-1)^{m+1}$.

*Proof sketch.* Write $s(a,b)=(-1)^{b(a+m)}$, the sign of $\phi\otimes\delta\theta$ on the block with target $C_a\boxtimes E_b$.
1. Degrees. $C\otimes E$ has zero objects outside $[0,m+n]$ and $C\otimes B$ outside $[0,m+n-1]$.
2. Symmetry. [Products commute with T](product-involution.md).
3. Boundary equation. By the [Leibniz rule](product-leibniz.md) and [Pushforward of products](product-push.md), $\partial(\phi\otimes\delta\theta)=\partial\phi\otimes\delta\theta+(-1)^m\phi\otimes\partial\delta\theta=(-1)^m\phi\otimes g_\%\theta=(1\otimes g)_\%\big((-1)^m\phi\otimes\theta\big)$, since $\partial\phi=0$. This is the source of the sign $(-1)^m$.
4. The boundary is Poincaré. $\big((-1)^m\phi\otimes\theta\big)_\natural=(-1)^m(\phi_\natural\otimes\theta_\natural)\circ\Xi$ ([Duality map of a product](product-duality-map.md)), an equivalence by [Tensor products of equivalences](product-equivalence.md).
5. Cones. The canonical isomorphism $K:C\otimes\mathcal C(g)\to\mathcal C(1\otimes g)$ needs no signs. From $C_a\boxtimes B_{b-1}$, the component to $C_a\boxtimes E_{b-1}$ is $(-1)^a(-1)^{b-1}1\boxtimes g$ in the source and $(-1)^{a+b-1}1\boxtimes g$ in the target; the components $(-1)^a1\boxtimes d$ and $d\boxtimes1$ agree on the nose.
6. Pair map. Let $\psi_g$ be the [pair map](../../base/pairs/pair-map.md) of the given pair and $\psi^\times$ that of the product. On the summand $C^*_{m-a}\boxtimes E^*_{n-b}$, both $\psi^\times$ and $K\circ(\phi_\natural\otimes\psi_g)\circ\Xi$ have $E$-component $s(a,b)\,\phi_a\boxtimes\delta\theta_b$ and $B$-component $(-1)^bs(a,b)\,\phi_a\boxtimes\theta_{b-1}g^*_{n-b}$. For $\psi^\times$ the second sign is $(-1)^{a+b}(-1)^m(-1)^{(b-1)(a+m)}=(-1)^bs(a,b)$. So $\psi^\times=K\circ(\phi_\natural\otimes\psi_g)\circ\Xi$, an equivalence by [Tensor products of equivalences](product-equivalence.md).

## Sources

- [Ranicki 1980 I, §8, products of complexes and pairs](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign computation in this paper's conventions.

## Depends on

- [Strict Poincaré pair](../../base/pairs/poincare-pair.md)
- [Tensor product of complexes](complex-product.md)
- [External product of structures](external-product.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Duals of box products](box-dual.md)

## Proof depends on

- [Leibniz rule for products](product-leibniz.md)
- [Products commute with T](product-involution.md)
- [Pushforward of products](product-push.md)
- [Duality map of a product](product-duality-map.md)
- [Tensor products of equivalences](product-equivalence.md)
- [Mapping cone](../../base/complexes/cone.md)
- [Pair map](../../base/pairs/pair-map.md)
