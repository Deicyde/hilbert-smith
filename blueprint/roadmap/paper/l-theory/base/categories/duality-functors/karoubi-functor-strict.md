---
article_id: af_e0742bde460a21d4ec802cb5
declaration: lemma
origin: background
statement: formalized
lean: HSP.DualFunctor.kar_isStrict
proof: formalized
---

# The completion of a strict duality functor is strict

If a [duality functor](../duality-functor.md) $(F,\xi):\mathcal A\to\mathcal B$ is [strict](strict-duality-functor.md), then so is its [completion](../karoubi-functor.md) $\mathrm{Kar}\,F:\mathrm{Kar}\,\mathcal A\to\mathrm{Kar}\,\mathcal B$.

*Proof sketch.* Let $(M,e)$ be an object of $\mathrm{Kar}\,\mathcal A$, with dual $(M^*,e^*)$. Strictness of $F$ gives $F(M^*)=F(M)^*$ with $\xi_M$ the identity, and then naturality of $\xi$ gives $F(e^*)=F(e)^*$. So $\mathrm{Kar}\,F(M^*,e^*)=(F(M^*),F(e^*))=(F(M)^*,F(e)^*)=(\mathrm{Kar}\,F(M,e))^*$, and its duality isomorphism $\xi_M\circ F(e^*)=F(e^*)$ is the identity of $(F(M^*),F(e^*))$.

## Sources

- [Ranicki 1992, §1](../../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Completion of a duality functor](../karoubi-functor.md)
- [Strict duality functor](strict-duality-functor.md)
- [Duality functor](../duality-functor.md)
- [Small Q-linear category with strict duality](../duality-category.md)
- [Idempotent completion with duality](../karoubi-duality.md)
