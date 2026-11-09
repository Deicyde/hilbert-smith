---
article_id: af_d954bb703e948a36e303def2
declaration: theorem
origin: bridged
---
# The chain model is Poincaré

For every $i$:
1. $\varphi_i:D_i^{N-*}\to D_i$ is a chain map with $T\varphi_i=\varphi_i$;
2. $b_i$ is a chain map, and it is the exact inverse of the unsymmetrized $\varphi^{\otimes n}\otimes\varphi_P$. There are $H_i,H'_i$ with $\varphi_ib_i-1=dH_i+H_id$ and $b_i\varphi_i-1=\delta H'_i+H'_i\delta$;
3. $\varphi_i,b_i,H_i,H'_i$ have $d_\infty$-propagation at most $h_i$ in torus labels;
4. $\varepsilon\varphi_i(\alpha)=\alpha(z_i)$ for $\alpha$ of degree $0$.

*Proof sketch.* (1) A tensor product of strict symmetric structures is strict symmetric [U]. (2) Telescope $\bigotimes_jA_j-1=\sum_j1^{\otimes(j-1)}\otimes(A_j-1)\otimes A_{j+1}\otimes\cdots$. The $j$-th term has homotopy $1\otimes\cdots\otimes K\otimes A_{j+1}\otimes\cdots$ by circle duality (3); the $P$ factor is exact. (3) Each factor moves only its own coordinate, by at most $h_i/2$; the composite homotopies use two factors. (4) Use circle duality (4), $\varepsilon\varphi_P(e_4^*)=1$, and the Koszul sign $(-1)^{n(n-1)/2}$ of pairing $n$ degree-one factors, which the sign in $z_i$ cancels.

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: replaces the cap-block comparison of HS paper, Section 7.
## Depends on
- [Chain-model duality](chain-model-duality.md)
## Proof depends on
- [Circle duality](circle-duality.md), [cells of CP^2](cp2-cells.md)
