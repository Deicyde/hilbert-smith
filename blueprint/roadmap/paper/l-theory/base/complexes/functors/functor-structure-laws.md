---
article_id: af_8bc80fa64aa22bf5882156de
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualFunctor.mapStructure_compat
proof: formalized
---

# Images of structures commute with the boundary, T and the duality map

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md) and $C$ a complex in $\mathcal B$. The [image of structures](functor-structure.md) $F_\%$ satisfies:
1. $\partial(F_\%\phi)=F_\%(\partial\phi)$ for every $\phi\in M(C)_n$, for the [boundary of the structure complex](../structure-complex.md);
2. $T(F_\%\phi)=F_\%(T\phi)$ for every $\phi\in M(C)_n$, for [the involution $T$](../structure-involution.md);
3. if $\phi\in M(C)_k$ and $F_\%\phi$ are cycles (the latter follows from the former by (1)), then the [duality map](../cycle-chain-map.md) of $F_\%\phi$ is
$$(F_\%\phi)_\natural=F(\phi_\natural)\circ\xi^{-1}:(FC)^{k-*}\to F(C^{k-*})\to FC,$$
with $\xi^{-1}$ the isomorphism of [Duality functors and dual complexes](functor-dual-iso.md).

*Proof sketch.* (1) On a component, both sides are sums of terms $F(d)\,F(\phi)\,\xi^{-1}$ and $F(\phi)\,F(d^*)\,\xi^{-1}$ with the same signs, and $F(d^*)\,\xi^{-1}=\xi^{-1}\,(Fd)^*$ by naturality of $\xi$. (2) $T$ dualizes a component and composes with the identification $M^{**}=M$; dualizing $\xi^{-1}_M$ gives $\xi^{-1}_{M^*}$ up to these identifications, because $\xi_M^*=\xi_{M^*}$, and naturality of $\xi$ moves it past $F(\phi^*)$. (3) Both sides are $F(\phi_{r,k-r})\circ\xi^{-1}_{C_{k-r}}$ in degree $r$.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Image of a complex under a duality functor](functor-complex.md)
- [Image of structures under a duality functor](functor-structure.md)
- [Duality functors and dual complexes](functor-dual-iso.md)
- [Structure complex](../structure-complex.md)
- [The involution T](../structure-involution.md)
- [Duality map of a cycle](../cycle-chain-map.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
- [Dual complex](../dual-complex.md)
