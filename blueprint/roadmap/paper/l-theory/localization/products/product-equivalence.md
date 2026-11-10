---
article_id: af_f2a78df55345e9814b62cb3f
declaration: lemma
origin: background
---

# Tensor products of equivalences

If $f:C\to C'$ is a chain homotopy equivalence of complexes in $\operatorname{Kar}\mathcal B$ and $g:E\to E'$ one of complexes in $C_\mathbb Z(\mathbb Q)$, all with finitely many nonzero chain objects, then $f\otimes g$ ([Tensor product of complexes over the line](complex-product.md)) is a chain homotopy equivalence.

*Proof sketch.* A homotopy $h:f\simeq f'$ gives $h\otimes g:f\otimes g\simeq f'\otimes g$, and $h':g\simeq g'$ gives $f\otimes g\simeq f\otimes g'$ through $(-1)^pf_p\boxtimes h'_q$. Apply this to the composites with homotopy inverses, using $(f'\otimes g')(f\otimes g)=f'f\otimes g'g$ (functoriality of the [box product](box-product.md)).

## Sources

- [Ranicki 1980 I, §8](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Tensor product of complexes over the line](complex-product.md)

## Proof depends on

- [Box product with a bounded vector space](box-product.md)
