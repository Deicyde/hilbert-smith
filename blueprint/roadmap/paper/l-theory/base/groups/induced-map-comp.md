---
article_id: af_2494f5c7d374657a08817f2b
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.LGroup.map_comp
proof: formalized
---

# Functoriality of induced maps

For duality functors $F:\mathcal B\to\mathcal B'$ and $G:\mathcal B'\to\mathcal B''$, $(G\circ F)_*=G_*\circ F_*:L_k(\mathcal B)\to L_k(\mathcal B'')$.

*Proof sketch.* $(GF)C=G(FC)$, and the composite $\xi$ gives $(GF)_\%\phi=G_\%F_\%\phi$.

## Sources

- New: direct

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md)
- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [Pushforward of structures](../complexes/structure-push.md)
