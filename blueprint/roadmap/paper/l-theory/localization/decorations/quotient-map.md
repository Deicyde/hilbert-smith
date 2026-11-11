---
article_id: af_a8764fcfed0ca053a9b86c8f
declaration: def
origin: background
---

# Quotient map into the decorated group

Let $\mathcal U\subset\mathcal A$ be as in [Decorated objects](decorated-object.md). The homomorphism
$$q^{\mathrm{im}}_*:L^p_k(\mathcal A)\to L^{\mathrm{im}}_k(\mathcal A/\mathcal U),\qquad [C,\phi]\mapsto[qC,q_\%\phi],$$
is the [induced homomorphism](../../base/groups/induced-map.md) of the strict duality functor $\mathrm{Kar}\,\mathcal A\to\mathrm{Dec}(\mathcal A/\mathcal U)$, $Q\mapsto qQ$.

*Proof sketch.* (The functor lands in $\mathrm{Dec}$.) $[qQ]$ is the class of an image, so $qQ$ is decorated. The corestriction of the strict duality functor $\mathrm{Kar}\,q$ to the full subcategory $\mathrm{Dec}(\mathcal A/\mathcal U)$ is again a strict duality functor, and [Induced homomorphism](../../base/groups/induced-map.md) applies.

## Sources

- New: the induced homomorphism of the quotient functor, with its decoration recorded

## Depends on

- [Decorated quotient L-group](decorated-l-group.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)
- [Decorated objects](decorated-object.md)
