---
article_id: af_0b59dce5290db42889e0670f
declaration: def
origin: background
statement: formalized
lean: HSP.Bounded.mapFunctor
---

# The entrywise functor

Let $F:A\to A'$ be an additive functor between small $\mathbb Q$-linear additive categories. The *entrywise functor* $C_\mathbb ZF:C_\mathbb Z(A)\to C_\mathbb Z(A')$ of the [bounded categories](bounded-category.md) sends an object $(M_n)$ to $(FM_n)$ and a bounded matrix $(f_{mn})$ to $(Ff_{mn})$. It is well defined because $Ff_{mn}=0$ whenever $f_{mn}=0$, so the propagation does not grow, and it is a functor because matrix products are finite sums and $F$ is additive. It is additive, and $\mathbb Q$-linear when $F$ is.

## Sources

- New: apply $F$ entrywise.

## Depends on

- [The bounded category](bounded-category.md)
