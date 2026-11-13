---
article_id: af_2ede78d607eb45f0a7205c70
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.cobordant_equivalence
---

# Cobordism is an equivalence relation

Cobordism of strict $k$-dimensional symmetric Poincaré complexes in a duality category $\mathcal B$ is reflexive, symmetric and transitive.

*Proof sketch.* Reflexive: [Homotopy-isometric complexes are cobordant](cylinder-cobordism.md) with $\mathcal P$ all objects, $h=1$ and $\chi=0$; this *reflexivity pair* is $((1,1):C\oplus C\to C,0,\phi\oplus(-\phi))$. Symmetric: given a pair $W$ with boundary $(C\oplus C',\phi\oplus(-\phi'))$, apply [Transport of pairs along isomorphisms](pair-transport.md) with $u$ the swap $C'\oplus C\to C\oplus C'$, $\phi''=(-\phi')\oplus\phi$ and $s=-1$; the new boundary is $(C'\oplus C,\phi'\oplus(-\phi))$. Transitive: given pairs $W_1$ and $W_2$ with boundaries $(C\oplus C',\phi\oplus(-\phi'))$ and $(C'\oplus C'',\phi'\oplus(-\phi''))$, $W_1\oplus W_2$ is a pair by [Sums of pairs](sum-of-pairs.md). Transport it ($s=1$) along the permutation $(C\oplus C'')\oplus(C'\oplus C')\to(C\oplus C')\oplus(C'\oplus C'')$, $(c,c'',x,y)\mapsto((c,x),(y,c''))$, to the boundary structure $(\phi\oplus(-\phi''))\oplus(-(\phi'\oplus(-\phi')))$. [Gluing](gluing.md) with $V_A$ the reflexivity pair of $(C',\phi')$ and $V_B$ the transported sum gives a pair with boundary $(C\oplus C'',\phi\oplus(-\phi''))$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]

## Depends on

- [Cobordism](cobordism.md)
- [Small Q-linear category with strict duality](../categories/duality-category.md)
- [Strict symmetric Poincaré complex](symmetric-poincare-complex.md)

## Proof depends on

- [Homotopy-isometric complexes are cobordant](cylinder-cobordism.md)
- [Transport of pairs along isomorphisms](pair-transport.md)
- [Sums of pairs](sum-of-pairs.md)
- [Gluing](gluing.md)
