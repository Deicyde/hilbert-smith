---
article_id: af_e1a888bd3aa3abe265e9fc4b
declaration: def
origin: background
statement: formalized
lean: HSP.ultL.map
---

# Induced map on ultimate L

Let $(F,\xi):\mathcal A\to\mathcal A'$ be a duality functor, not necessarily strict, and let $C_{\mathbb Z^j}F:C_{\mathbb Z^j}\mathcal A\to C_{\mathbb Z^j}\mathcal A'$ be its $j$-fold bounded extension, with $\xi$ applied entrywise ($C_{\mathbb Z^0}F=F$). $F_*:\mathbb L_k(\mathcal A)\to\mathbb L_k(\mathcal A')$ is the homomorphism of colimits induced by the levelwise homomorphisms $(C_{\mathbb Z^j}F)_*:L^{\langle -j\rangle}_k(\mathcal A)\to L^{\langle -j\rangle}_k(\mathcal A')$, which commute with $t$ by [Naturality of the transition](../../localization/transitions/transition-naturality.md). (Lean: $\mathcal A$ and $\mathcal A'$ have the same universe levels, so that both colimits are taken in one category of abelian groups.)

## Sources

- New: levelwise maps commuting with $t$.

## Depends on

- [Ultimate L-group](ultimate-l-group.md)
- [Sequence of lower L-groups](lower-l-sequence.md)
- [Induced homomorphism](../../base/groups/induced-map.md)
- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Naturality of the transition](../../localization/transitions/transition-naturality.md)
