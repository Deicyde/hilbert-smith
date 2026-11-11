---
article_id: af_ae60322db6daee68fe6d3a3a
declaration: instance
origin: background
statement: formalized
proof: formalized
lean: HSP.Bounded.isDualAdditive_subPow
---

# Iterated bounded subcategories are closed under sums and duals

If $\mathcal U\subset\mathcal A$ is a full additive subcategory closed under the duality, so is every [iterated bounded subcategory](iterated-bounded-sub.md) $C_{\mathbb Z^j}\mathcal U\subset C_{\mathbb Z^j}\mathcal A$.

*Proof sketch.* Induction on $j$, applying [the bounded subcategory is closed under sums and duals](bounded-sub-additive.md) at each step.

## Sources

- New: closure properties of $C_{\mathbb Z^j}\mathcal U$.

## Depends on

- [Iterated bounded subcategories](iterated-bounded-sub.md), [the bounded subcategory is closed under sums and duals](bounded-sub-additive.md)
