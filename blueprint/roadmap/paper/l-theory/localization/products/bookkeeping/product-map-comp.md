---
article_id: af_3097b1cc54a15d9042f6966f
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProdMap_comp
proof: formalized
---

# Tensor products of chain maps compose

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and let $f:C\to C'$, $f':C'\to C''$, $g:E\to E'$, $g':E'\to E''$ be chain maps of complexes each with all but finitely many chain objects zero objects. Then $(f'f)\otimes(g'g)=(f'\otimes g')(f\otimes g)$ as [tensor products of chain maps](product-map.md).

*Proof sketch.* On the summand $C_p\boxtimes E_q$ both sides are $f'_pf_p\boxtimes g'_qg_q=(f'_p\boxtimes g'_q)(f_p\boxtimes g_q)$, since $\boxtimes$ is a functor.

## Sources

- New: functoriality, direct from the definition.

## Depends on

- [Duality pairings](../duality-pairing.md)
- [Tensor product of chain maps](product-map.md)
- [Small Q-linear category with strict duality](../../../base/categories/duality-category.md)
- [Tensor product of complexes](../complex-product.md)

## Proof depends on

- [A duality pairing is additive in the first variable](pairing-additive-left.md)
- [A duality pairing is additive in the second variable](pairing-additive-right.md)
- [The sums in a tensor product of complexes exist](product-sums-exist.md)
- [Signs for tensor products of chain complexes](tensor-signs.md)
