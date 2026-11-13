---
article_id: af_141197fa49d15318822918c1
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualFunctor.mapStructure_sum
proof: formalized
---

# Duality functors preserve sums of structures

Let $(F,\xi):\mathcal B\to\mathcal B'$ be a [duality functor](../../categories/duality-functor.md), $X,Y$ complexes in $\mathcal B$, and $\phi\in M(X)_n$, $\psi\in M(Y)_n$. Let $e:FX\oplus FY\to F(X\oplus Y)$ be the canonical isomorphism, with components $F(\mathrm{in}_X)$ and $F(\mathrm{in}_Y)$. Then the [pushforward](../structure-push.md) along $e$ carries the [sum](../sum-of-complexes.md) of the [images](functor-structure.md) to the image of the sum:
$$e_\%(F_\%\phi\oplus F_\%\psi)=F_\%(\phi\oplus\psi).$$

*Proof sketch.* By definition $\phi\oplus\psi=(\mathrm{in}_X)_\%\phi+(\mathrm{in}_Y)_\%\psi$, and similarly for the images. Since $e\circ\mathrm{in}_{FX}=F(\mathrm{in}_X)$, [functoriality of the pushforward](push-comp.md) gives $e_\%(\mathrm{in}_{FX})_\%F_\%\phi=F(\mathrm{in}_X)_\%F_\%\phi=F_\%((\mathrm{in}_X)_\%\phi)$ by [Duality functors commute with pushforward](../functor-push.md), and likewise for $\psi$; $F_\%$ is additive.

## Sources

- New: direct from the definitions.

## Depends on

- [Duality functor](../../categories/duality-functor.md)
- [Image of structures under a duality functor](functor-structure.md)
- [Image of a complex under a duality functor](functor-complex.md)
- [Pushforward of structures](../structure-push.md)
- [Sum of structured complexes](../sum-of-complexes.md)
- [Small Q-linear category with strict duality](../../categories/duality-category.md)
- [A duality category has binary direct sums](../../categories/sums/dual-binary-biproducts.md)
- [Structure complex](../structure-complex.md)

## Proof depends on

- [Pushforward preserves composition](push-comp.md)
- [Duality functors commute with pushforward](../functor-push.md)
