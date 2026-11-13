---
article_id: af_7bcc6b4535342f072a225a2f
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.middleForm_sum
---

# Middle form of a sum

For strict 4-dimensional symmetric Poincaré complexes $(C,\varphi)$ and $(C',\varphi')$ in $\mathrm{Kar}\,\mathrm{Free}(\mathbb Q[G])$ and a third one equal, as a structured complex, to their [sum](../../l-theory/base/complexes/sum-of-complexes.md) $(C\oplus C',\varphi\oplus\varphi')$, the map $H^2(C\oplus C';\mathbb R)\to H^2(C;\mathbb R)\oplus H^2(C';\mathbb R)$ induced on real cochains by the transposes of the two inclusions (on coordinates, the projections of the cochains onto the two blocks) is a bijective $G$-equivariant isometry from $b_{C\oplus C'}$ to $b_C\perp b_{C'}$.

*Proof sketch.* Real cochains of a sum are the sum of the real cochains, with the coboundary acting blockwise, so cohomology splits. $(\varphi\oplus\varphi')_2$ is block diagonal and the pairing is the block sum, so the form is the orthogonal sum.

## Sources

- New: block computation.

## Depends on

- [The middle form](middle-form.md)
- [The map on real cohomology induced by a chain map](../real/real-cohomology-map.md)
- [The action of the group on real cohomology](../real/real-cohomology-action.md)
- [Sum of structured complexes](../../l-theory/base/complexes/sum-of-complexes.md)
- [Free category of a finite group](../../categories/asymptotic/free-category.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Idempotent completion with duality](../../l-theory/base/categories/karoubi-duality.md)
- [A duality category has binary direct sums](../../l-theory/base/categories/sums/dual-binary-biproducts.md)
- [Structure complex](../../l-theory/base/complexes/structure-complex.md)
- [Strict symmetric Poincaré complex](../../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Real cohomology](../real/real-cohomology.md)
- [The real matrix of a morphism](../real/real-matrix.md)
