---
article_id: af_06840cffe4b2218fe1bf529d
declaration: def
origin: background
statement: formalized
lean: HSP.KaroubiFiltration.top
---

# The whole filtration

Let $\mathcal B$ be a [duality category](duality-category.md). All objects of $\mathcal B$ form a [full additive subcategory closed under duality](dual-additive-subcategory.md): it contains a zero object, a sum of any two of its objects, and the dual of each of its objects. The *whole filtration* of $\mathcal B$ is the [involution-invariant Karoubi filtration](karoubi-filtration.md) of $\mathcal B$ by all objects with $\mathcal D(M)=\{1_M\}$ for every object $M$: $1_M$ is idempotent, splits through $M$ itself, and $1-1_M=0$ splits through a zero object; each $\mathcal D(M)$ is a singleton, so it is nonempty and directed; $1_M$ satisfies $1_Mg=g$ and $h1_M=h$; and $p=1_M$ if and only if $p^*=1_{M^*}$.

## Sources

- New: a toy filtration, used as a witness that the structures built from filtrations can be realized.

## Depends on

- [Small Q-linear category with strict duality](duality-category.md)
- [Additive subcategory closed under duality](dual-additive-subcategory.md)
- [Involution-invariant Karoubi filtration](karoubi-filtration.md)
