---
article_id: af_bc37b9efd9f2661bfeaf5a67
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cobordant_sum_laws
proof: formalized
---

# Sum of Poincaré complexes up to cobordism

Let $\mathcal B$ be a duality category and use the [sum](../pairs/poincare-sum.md), [negative](../pairs/poincare-neg.md) and [zero](../pairs/poincare-zero.md) of strict $k$-dimensional symmetric Poincaré complexes. Up to [cobordism](../pairs/cobordism.md):
1. if $(C_1,\phi_1)$ is cobordant to $(C'_1,\phi'_1)$ and $(C_2,\phi_2)$ to $(C'_2,\phi'_2)$, then $(C_1,\phi_1)\oplus(C_2,\phi_2)$ is cobordant to $(C'_1,\phi'_1)\oplus(C'_2,\phi'_2)$;
2. if $(C,\phi)$ is cobordant to $(C',\phi')$, then $(C,-\phi)$ is cobordant to $(C',-\phi')$;
3. $((C,\phi)\oplus(C',\phi'))\oplus(C'',\phi'')$ is cobordant to $(C,\phi)\oplus((C',\phi')\oplus(C'',\phi''))$;
4. $(C,\phi)\oplus(C',\phi')$ is cobordant to $(C',\phi')\oplus(C,\phi)$;
5. $(0,0)\oplus(C,\phi)$ is cobordant to $(C,\phi)$;
6. $(C,-\phi)\oplus(C,\phi)$ is cobordant to $(0,0)$.

*Proof sketch.* (1) Given cobordisms $W_1$ and $W_2$, $W_1\oplus W_2$ is a pair by [Sums of pairs](../pairs/sum-of-pairs.md). Along the permutation of its boundary summands it is a cobordism from $(C_1\oplus C_2,\phi_1\oplus\phi_2)$ to $(C'_1\oplus C'_2,\phi'_1\oplus\phi'_2)$ by [Transported pairs are cobordisms](../pairs/transport-cobordism.md) with $s=1$. (2) The same with a cobordism $W$, $u=1$ and $s=-1$. (3)-(5) The canonical isomorphisms carry the structures exactly, so [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md) gives the cobordisms. (6) The reflexivity pair $((1,1):C\oplus C\to C,0,\phi\oplus(-\phi))$ is the pair of [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md) for $h=1_C$ and $\chi=0$. Along the isomorphism $(C\oplus C)\oplus0\cong C\oplus C$ with $s=-1$ it gives, by [Transported pairs are cobordisms](../pairs/transport-cobordism.md), a cobordism from $(C,-\phi)\oplus(C,\phi)$ to $(0,0)$, since $-((-\phi)\oplus\phi)=\phi\oplus(-\phi)$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [The sum of two Poincaré complexes](../pairs/poincare-sum.md)
- [Negative of a Poincaré complex](../pairs/poincare-neg.md)
- [Zero Poincaré complex](../pairs/poincare-zero.md)
- [Cobordism](../pairs/cobordism.md)

## Proof depends on

- [Sums of pairs](../pairs/sum-of-pairs.md)
- [Transported pairs are cobordisms](../pairs/transport-cobordism.md)
- [Isomorphic Poincaré complexes are cobordant](../pairs/iso-cobordism.md)
- [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md)
