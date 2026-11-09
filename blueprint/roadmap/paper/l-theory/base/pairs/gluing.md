---
article_id: af_5cd78768c8847858e79c03a6
declaration: lemma
origin: bridged
---

# Gluing

$V_A\cup_CV_B$ is a strict $n$-dimensional Poincaré pair with boundary $(C_B,\phi_B)$.

*Proof sketch.* (0) Boundary. Componentwise from the same facts for $(C_B\oplus C,\phi_B\oplus(-\phi))$: $\phi_B$ is a cycle with $T\phi_B=\phi_B$, and $C_{B,r}$, a summand of a zero object, is a zero object for $r$ outside $[0,n-1]$. $(\phi_B\oplus(-\phi))_\natural=\phi_{B\natural}\oplus(-\phi_\natural)$, so $\phi_{B\natural}$ is an equivalence by [Sums of equivalences](../complexes/sum-equivalence.md). $U_r=D_{A,r}\oplus D_{B,r}\oplus C_{r-1}$ is a zero object for $r$ outside $[0,n]$. (1) $T\Phi=\Phi$ follows from $T\delta\phi_\bullet=\delta\phi_\bullet$ and $T\phi=\phi$. (2) $\partial\Phi=g_{B\%}\phi_B$ holds blockwise, from $\partial\delta\phi_A=h_{A\%}\phi$, $\partial\delta\phi_B=g_{B\%}\phi_B-h_{B\%}\phi$ and $\partial\phi=0$. (3) Let $X\in M(U)_{n+1}$ have the single entry $X_r=\tfrac{(-1)^{n+r}}2\phi_{r-1}$ in the slot $(C_{r-1},C^*_{n-r})$. Then $\Phi'=\Phi-\partial X$ has entry $(-1)^nh_A\phi_r$ at $(D_A,C^*)$ and $-(-1)^r\phi_{r-1}h_B^*$ at $(C,D_B^*)$, and zero at $(D_B,C^*)$ and $(C,D_A^*)$. By [Pair maps of homologous data](pair-map-homotopy.md), the pair map $\Psi'$ of $(\Phi',\phi_B)$ is homotopic to that of $(\Phi,\phi_B)$. (4) $U^{n-*}=\mathcal C(h_A)^{n-*}\oplus_\tau D_B^{n-*}$, dual to $U\to\mathcal C(h_A)$, and $\mathcal C(g_B)=D_A\oplus_{\tau'}\mathcal C((g_B,h_B))$, as [twisted sums](../complexes/twisted-sum.md). $\Psi'$ is [triangular](../complexes/triangular-map.md) with diagonal components $\psi_A^\flat$ and $\psi_B$. These are equivalences by [Dual form of the pair map](dual-pair-map.md) and the hypothesis on $V_B$. Conclude by [Triangular equivalences](../complexes/triangular-equivalence.md).

## Sources

- [Ranicki 1980 I, §3](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the strict coefficients and the homotopy $X$

## Depends on

- [Algebraic union](algebraic-union.md)

## Proof depends on

- [Sums of equivalences](../complexes/sum-equivalence.md)
- [Pair maps of homologous data](pair-map-homotopy.md)
- [Twisted sum](../complexes/twisted-sum.md)
- [Triangular map](../complexes/triangular-map.md)
- [Dual form of the pair map](dual-pair-map.md)
- [Triangular equivalences](../complexes/triangular-equivalence.md)
