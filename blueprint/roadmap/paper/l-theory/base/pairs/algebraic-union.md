---
article_id: af_3ad13a8f61ffdf068cf8aaf8
declaration: def
origin: bridged
---

# Algebraic union

Let $V_A=(h_A:C\to D_A,\delta\phi_A,\phi)$ and $V_B=((g_B,h_B):C_B\oplus C\to D_B,\delta\phi_B,\phi_B\oplus(-\phi))$ be strict $n$-dimensional pairs. Their *union* $V_A\cup_CV_B$ is $(g_B:C_B\to U,\Phi,\phi_B)$, where $U=\mathcal C((h_A,h_B):C\to D_A\oplus D_B)$ and $g_B$ lands in $D_B\subset U$. The structure is
$$\Phi_r=\begin{pmatrix}\delta\phi_{A,r}&0&\tfrac{(-1)^n}{2}h_A\phi_r\\0&\delta\phi_{B,r}&-\tfrac{(-1)^n}{2}h_B\phi_r\\\tfrac{(-1)^r}{2}\phi_{r-1}h_A^*&-\tfrac{(-1)^r}{2}\phi_{r-1}h_B^*&0\end{pmatrix},$$
with rows $D_{A,r},D_{B,r},C_{r-1}$ and columns $D^*_{A,n-r},D^*_{B,n-r},C^*_{n-r-1}$.

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the halves are the unique constants of this block shape solving $T\Phi=\Phi$ and $\partial\Phi=g_{B\%}\phi_B$

## Depends on

- [Strict Poincaré pair](poincare-pair.md)
- [Mapping cone](../complexes/cone.md)
- [Sum of structured complexes](../complexes/sum-of-complexes.md)
