---
article_id: af_bc5196e8423810862b6c4b39
declaration: def
origin: background
statement: formalized
lean: HSP.DualCat.dualBiprodIso
---

# Dual of a binary sum

Let $M,N$ be objects of a [duality category](../duality-category.md) $\mathcal B$, with inclusions $\iota_M,\iota_N$ and projections $\pi_M,\pi_N$ of $M\oplus N$. The map $(M\oplus N)^*\to M^*\oplus N^*$ with components $\iota_M^*,\iota_N^*$ is an isomorphism. Its inverse $M^*\oplus N^*\to(M\oplus N)^*$ is $\pi_M^*$ on $M^*$ and $\pi_N^*$ on $N^*$. Unfolding: the inverse followed by $\iota_M^*$ is the projection onto $M^*$, and the inverse followed by $\iota_N^*$ is the projection onto $N^*$.

*Proof sketch.* The composite in one order is $\pi_M^*\iota_M^*+\pi_N^*\iota_N^*=(\iota_M\pi_M+\iota_N\pi_N)^*=\mathrm{id}^*=\mathrm{id}$. In the other order the entries are $\iota_B^*\pi_A^*=(\pi_A\iota_B)^*$ for $A,B\in\{M,N\}$, which are the identity for $A=B$ and zero otherwise. The unfolding statements are the same computation.

## Sources

- New: the canonical isomorphism, used for sums of duality functors and for duals of sums of decorated objects.

## Depends on

- [Small Q-linear category with strict duality](../duality-category.md)
