---
article_id: af_bc37b9efd9f2661bfeaf5a67
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cobordant_sum_laws
---

# Sum of Poincaré complexes up to cobordism

Let $\mathcal B$ be a duality category and use the sum, negation and zero of strict $k$-dimensional symmetric Poincaré complexes of [Sums of Poincaré complexes](../pairs/sum-of-poincare.md). Up to [cobordism](../pairs/cobordism.md):
1. if $(C_1,\phi_1)$ is cobordant to $(C'_1,\phi'_1)$ and $(C_2,\phi_2)$ to $(C'_2,\phi'_2)$, then $(C_1,\phi_1)\oplus(C_2,\phi_2)$ is cobordant to $(C'_1,\phi'_1)\oplus(C'_2,\phi'_2)$;
2. if $(C,\phi)$ is cobordant to $(C',\phi')$, then $(C,-\phi)$ is cobordant to $(C',-\phi')$;
3. $((C,\phi)\oplus(C',\phi'))\oplus(C'',\phi'')$ is cobordant to $(C,\phi)\oplus((C',\phi')\oplus(C'',\phi''))$;
4. $(C,\phi)\oplus(C',\phi')$ is cobordant to $(C',\phi')\oplus(C,\phi)$;
5. $(0,0)\oplus(C,\phi)$ is cobordant to $(C,\phi)$;
6. $(C,-\phi)\oplus(C,\phi)$ is cobordant to $(0,0)$.

*Proof sketch.* (1) Given cobordisms $W_1$ and $W_2$, $W_1\oplus W_2$ is a pair by [Sums of pairs](../pairs/sum-of-pairs.md), and [Transport of pairs along isomorphisms](../pairs/pair-transport.md) ($s=1$) along the permutation of its boundary summands makes it a cobordism from $(C_1\oplus C_2,\phi_1\oplus\phi_2)$ to $(C'_1\oplus C'_2,\phi'_1\oplus\phi'_2)$. (2) Transport a cobordism $W$ with $u=1$ and $s=-1$. (3)-(5) The canonical isomorphisms carry the structures exactly, so [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md) with $\chi=0$ gives the cobordisms. (6) The reflexivity pair $((1,1):C\oplus C\to C,0,\phi\oplus(-\phi))$, transported along the unitary isomorphism $(C\oplus C)\oplus0\cong C\oplus C$ and the swap of the summands, is a cobordism from $(C,-\phi)\oplus(C,\phi)$ to $(0,0)$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Sums of Poincaré complexes](../pairs/sum-of-poincare.md)
- [Cobordism](../pairs/cobordism.md)

## Proof depends on

- [Sums of pairs](../pairs/sum-of-pairs.md)
- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md)
