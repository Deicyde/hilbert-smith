---
article_id: af_84e10c0b4db6fd9cd6b651e1
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.LGroup.map_eq_of_unitaryIso
proof: formalized
---

# Unitary invariance

If $\eta:F\cong G$ is a unitary natural isomorphism of duality functors $\mathcal B\to\mathcal B'$, then $F_*=G_*:L_k(\mathcal B)\to L_k(\mathcal B')$.

*Proof sketch.* (1) $\eta_C:FC\to GC$ is an isomorphism of complexes. (2) Naturality and unitarity give $\eta_{C\%}F_\%\phi=G_\%\phi$. (3) So $\eta_C$ is an isomorphism $F(C,\phi)\cong G(C,\phi)$ carrying the structures, and [isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md), so $[F(C,\phi)]=[G(C,\phi)]$.

## Sources

- New: direct; the HS paper does not state this property

## Depends on

- [Unitary natural isomorphism](../categories/unitary-isomorphism.md)
- [Induced homomorphism](induced-map.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Duality functor](../categories/duality-functor.md)
- [Group structure on L](l-group-add.md)
- [L-group](l-group.md)

## Proof depends on

- [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md)
- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [Pushforward of structures](../complexes/structure-push.md)
- [Structure complex](../complexes/structure-complex.md)
- [Strict symmetric Poincaré complex](../pairs/symmetric-poincare-complex.md)
