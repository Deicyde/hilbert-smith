---
article_id: af_f2a78df55345e9814b62cb3f
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.cxProd_homotopyEquiv
---

# Tensor products of equivalences

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md). If $f:C\to C'$ is a chain homotopy equivalence of complexes in $\mathcal B$ and $g:E\to E'$ one of complexes in $\mathcal E$, all with finitely many nonzero chain objects, then $f\otimes g$ ([Tensor product of complexes](complex-product.md)) is a chain homotopy equivalence.

*Proof sketch.* A homotopy $h:f\simeq f'$ gives $h\otimes g:f\otimes g\simeq f'\otimes g$, and $h':g\simeq g'$ gives $f\otimes g\simeq f\otimes g'$ through $(-1)^pf_p\boxtimes h'_q$. Apply this to the composites with homotopy inverses, using $(f'\otimes g')(f\otimes g)=f'f\otimes g'g$ (functoriality of $\boxtimes$).

## Sources

- [Ranicki 1980 I, §8](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Duality pairings](duality-pairing.md)
- [Tensor product of complexes](complex-product.md)
- [Tensor product of chain maps](bookkeeping/product-map.md)

## Proof depends on

- [Tensor product of complexes](complex-product.md)
- [Tensor products of chain maps compose](bookkeeping/product-map-comp.md)
- [Tensor product of identities](bookkeeping/product-map-id.md)
