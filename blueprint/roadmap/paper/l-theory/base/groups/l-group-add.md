---
article_id: af_a376b5aa3925993024cfc900
declaration: def
origin: bridged
---

# Group structure on L^p

$L^p_k(\mathcal A)$ is an abelian group with $[C,\phi]+[C',\phi']=[C\oplus C',\phi\oplus\phi']$, zero $[0,0]$ and negation $-[C,\phi]=[C,-\phi]$.

*Proof sketch.* (1) Addition is well defined: given cobordisms $W_1$ and $W_2$, $W_1\oplus W_2$ is a pair by [Sums of pairs](../pairs/sum-of-pairs.md), and [Transport of pairs along isomorphisms](../pairs/pair-transport.md) ($s=1$) along the permutation of its boundary summands makes it a cobordism from $(C_1\oplus C_2,\phi_1\oplus\phi_2)$ to $(C'_1\oplus C'_2,\phi'_1\oplus\phi'_2)$. (2) Negation is well defined: transport a cobordism $W$ with $u=1$ and $s=-1$. (3) Associativity, commutativity and the unit come from canonical isomorphisms that carry structures exactly, by [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md) with $\chi=0$. (4) Inverse law: the reflexivity pair $((1,1):C\oplus C\to C,0,\phi\oplus(-\phi))$, transported along the unitary isomorphism $(C\oplus C)\oplus0\cong C\oplus C$, is a cobordism from $(C\oplus C,\phi\oplus(-\phi))$ to $(0,0)$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Projective L-group](l-group.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)

## Proof depends on

- [Sums of pairs](../pairs/sum-of-pairs.md)
- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Homotopy-isometric complexes are cobordant](../pairs/cylinder-cobordism.md)
