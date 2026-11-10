---
article_id: af_e88de6ae2d6490d7dc9286d7
declaration: def
origin: background
---

# Box product with a bounded vector space

Let $\mathcal B$ be a duality category and $\mathbb Q$ the duality category of [based vector spaces](based-vector-spaces.md). The *box product* is the $\mathbb Q$-bilinear functor
$$\boxtimes:\operatorname{Kar}\mathcal B\times C_\mathbb Z(\mathbb Q)\to\operatorname{Kar}C_\mathbb Z(\mathcal B).$$
For $N=(M,e)$ and $V=(\mathbb Q^{d_n})_n$, $N\boxtimes V$ has $M^{\oplus d_n}$ in position $n$ and the idempotent $e$ on each summand. For $f:N\to N'$ and $g:V\to V'$, the component $(f\boxtimes g)_{mn}$ is the block matrix whose $(i,i')$ entry is $(g_{mn})_{ii'}\,f$. So $f\boxtimes g$ has the propagation of $g$. When $\mathcal B=C_{\mathbb Z^j}\mathcal A$, the target is $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$ and the new coordinate is the outermost one.

*Proof sketch.* (The functor and bilinearity obligations.) $(f'f)\boxtimes(g'g)=(f'\boxtimes g')(f\boxtimes g)$ because the $(i,i'')$ entry of $g'_{lm}g_{mn}$ is $\sum_{i'}(g'_{lm})_{ii'}(g_{mn})_{i'i''}$ and $f'f$ is bilinear in its entries. Identities go to identities, $e$ being the identity of $N$. Bilinearity holds entrywise.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Based vector spaces](based-vector-spaces.md)
- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [The bounded category](../../bounded/categories/bounded-category.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
