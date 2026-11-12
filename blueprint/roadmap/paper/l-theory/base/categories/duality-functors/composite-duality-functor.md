---
article_id: af_18281b8732c8a1c9547f1aca
declaration: def
origin: background
statement: formalized
lean: HSP.DualFunctor.id, HSP.DualFunctor.comp
---

# Identity and composite duality functors

Let $\mathcal A,\mathcal B,\mathcal E$ be [duality categories](../duality-category.md).
- The *identity duality functor* of $\mathcal A$ is the identity functor $1_{\mathcal A}$ with $\xi=\mathrm{id}$.
- The *composite* of [duality functors](../duality-functor.md) $(F,\xi):\mathcal A\to\mathcal B$ and $(G,\zeta):\mathcal B\to\mathcal E$ is the duality functor $(G,\zeta)\circ(F,\xi)=(GF,\xi^{GF}):\mathcal A\to\mathcal E$, with
$$\xi^{GF}_M=\zeta_{FM}\circ G(\xi_M):\ GF(M^*)\to G(F(M)^*)\to GF(M)^*.$$

*Proof sketch.* (That these are duality functors.) For the identity, the conditions are identities. $GF$ is $\mathbb Q$-linear because $F$ and $G$ are. Naturality of $\xi^{GF}$ follows from the naturality of $\xi$ and of $\zeta$ at $F(f)$. For $(\xi^{GF}_M)^*=\xi^{GF}_{M^*}$, apply $G$ to $(\xi_M)^*=\xi_{M^*}$, use $(\zeta_{F(M^*)})^*=\zeta_{F(M^*)^*}$ and move $\zeta$ past $G((\xi_M)^*)$ by naturality, the transports along $X^{**}=X$ cancelling.

## Sources

- [Ranicki 1992, §1](../../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Duality functor](../duality-functor.md)
- [Small Q-linear category with strict duality](../duality-category.md)
