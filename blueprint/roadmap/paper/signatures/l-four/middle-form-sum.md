---
article_id: af_7bcc6b4535342f072a225a2f
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.middleForm_sum
---

# Middle form of a sum

For strict 4-dimensional complexes $(C,\varphi)$ and $(C',\varphi')$, the map $H^2(C\oplus C';\mathbb R)\to H^2(C;\mathbb R)\oplus H^2(C';\mathbb R)$ induced on real cochains by the transposes of the two inclusions (on coordinates, the projections of the cochains onto the two blocks) is a bijective $G$-equivariant isometry from $b_{C\oplus C'}$ to $b_C\perp b_{C'}$.

*Proof sketch.* Real cochains of a sum are the sum of the real cochains, with the coboundary acting blockwise, so cohomology splits. $(\varphi\oplus\varphi')_2$ is block diagonal and the pairing is the block sum, so the form is the orthogonal sum.

## Sources

- New: block computation.

## Depends on

- [The middle form](middle-form.md)
- [The map on real cohomology induced by a chain map](../real/real-cohomology-map.md)
- [The action of the group on real cohomology](../real/real-cohomology-action.md)
- [Sums of Poincaré complexes](../../l-theory/base/pairs/sum-of-poincare.md)
