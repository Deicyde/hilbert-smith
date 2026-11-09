---
declaration: def
origin: bridged
---

# Support Mayer-Vietoris functor

Let $\Lambda_X$ be the lattice of closed $C_p$-invariant subsets of $X$, ordered by inclusion, with $\vee=\cup$ and $\wedge=\cap$. The following data form a Mayer-Vietoris functor on $\Lambda_X$:
- $F_k(S)=\mathbb L_k(\mathcal A_S)$, where $\mathcal A_S$ is the support subcategory;
- $i_{S\le S'}$ is induced by the inclusion $\mathcal A_S\subset\mathcal A_{S'}$;
- $\partial_{A,B}$ is the excision boundary of the excisive pair $(\mathcal A_A,\mathcal A_B)$ in $\mathcal A_{A\cup B}$.

*Proof sketch.*
1. The inclusions are strict duality functors, so they induce maps on $\mathbb L_k$. The identity and composition laws hold because the induced maps of equal functors are equal.
2. Relative support calculus says that $(\mathcal A_A,\mathcal A_B)$ is an excisive pair in $\mathcal A_{A\cup B}$ with $\mathcal A_A\cap\mathcal A_B=\mathcal A_{A\cap B}$. So the excision boundary lands in $\mathbb L_{k-1}(\mathcal A_{A\cap B})$.
3. Middle exactness is Mayer-Vietoris middle exactness for this pair.

## Sources

- HS paper, Section 2 (support calculus).
- HS paper, Section 4 (Nilpotence) and Section 6 (Localization boundaries).

## Depends on

- [Mayer-Vietoris functor](mayer-vietoris-functor.md)
- [Support subcategory](../categories/support-subcategory.md)
- [Relative support calculus](../categories/relative-support-excisive.md)
- [Induced map on ultimate L](../l-theory/ultimate/induced-map.md)
- [Excision boundary](../l-theory/ultimate/excision-boundary.md)

## Proof depends on

- [Mayer-Vietoris middle exactness](../l-theory/ultimate/mayer-vietoris-middle.md)
