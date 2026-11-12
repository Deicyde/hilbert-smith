---
article_id: af_025d7518fc54114194a1f20f
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualFunctor.mapStructure_pushforward
proof: formalized
---

# Duality functors commute with pushforward

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../categories/duality-functor.md), $f:C\to D$ a chain map and $\phi\in M(C)_n$. Then
$$F_\%(f_\%\phi)=(Ff)_\%(F_\%\phi)$$
in $M(FD)_n$, for the [pushforward](structure-push.md) and the [image of structures under $F$](functors/functor-structure.md).

*Proof sketch.* On the component $(p,q)$ both sides are $F(f_p)F(\phi_{p,q})F(f_q^*)\xi^{-1}_{D_q}=F(f_p)F(\phi_{p,q})\xi^{-1}_{C_q}(Ff_q)^*$, by naturality of $\xi$.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../categories/duality-functor.md)
- [Pushforward of structures](structure-push.md)
- [Image of structures under a duality functor](functors/functor-structure.md)
