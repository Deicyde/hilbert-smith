---
article_id: af_eceb766fabf0377b868964e6
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.LGroup.map_biprod
proof: formalized
---

# Sums of functors

For duality functors $(F,\xi),(G,\zeta):\mathcal B\to\mathcal B'$, let $F\oplus G$ be their [sum](../categories/sums/duality-functor-sum.md): $M\mapsto FM\oplus GM$, with $\xi\oplus\zeta$ followed by the canonical isomorphism $(FM\oplus GM)^*\cong FM^*\oplus GM^*$. Then $(F\oplus G)_*=F_*+G_*:L_k(\mathcal B)\to L_k(\mathcal B')$.

*Proof sketch.* The inclusions and projections of the summands $F C_r\oplus G C_r$ give an isomorphism of complexes $u:FC\oplus GC\cong(F\oplus G)C$. It carries the [sum](../complexes/sum-of-complexes.md) $F_\%\phi\oplus G_\%\phi$ to $(F\oplus G)_\%\phi$: by [pushforward of a composite](../complexes/functors/push-comp.md), $u_\%(F_\%\phi\oplus G_\%\phi)=(u\iota)_\%F_\%\phi+(u\iota')_\%G_\%\phi$, and in degree $(p,q)$ both sides are maps $(FC_q\oplus GC_q)^*\to FC_p\oplus GC_p$ whose component into $FC_p$ is $F(\phi_{p,q})\,\xi^{-1}\,\iota^*$ and whose component into $GC_p$ is $G(\phi_{p,q})\,\zeta^{-1}\,\iota'^*$. Since $(C,\phi)\oplus(C',\phi')$ is isomorphic to $(C\oplus C',\phi\oplus\phi')$ compatibly with the structures, $[(F\oplus G)(C,\phi)]=[F(C,\phi)\oplus G(C,\phi)]$ by [isomorphism invariance of cobordism](../pairs/iso-cobordism.md). Conclude with the addition of [Group structure on L](l-group-add.md).

## Sources

- New: direct

## Depends on

- [Induced homomorphism](induced-map.md)
- [Sum of duality functors](../categories/sums/duality-functor-sum.md)

## Proof depends on

- [Group structure on L](l-group-add.md)
- [The sum of two Poincaré complexes](../pairs/poincare-sum.md)
- [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
- [Pushforward preserves composition](../complexes/functors/push-comp.md)
- [Pushforward along the identity](../complexes/functors/push-id.md)
- [Duality functors carry Poincaré complexes](../pairs/functor-poincare.md)
- [Image of structures under a duality functor](../complexes/functors/functor-structure.md)
- [Image of a complex under a duality functor](../complexes/functors/functor-complex.md)
