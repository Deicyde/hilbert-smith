---
article_id: af_8126f50ba0f256052d6e2636
declaration: lemma
origin: bridged
---

# The test map is homotopic to the identity

For a local datum and $0<\rho<\rho_+$, the test map $f$ is homotopic to $\mathrm{id}_{S^n}$ relative to $\{\infty\}$.

*Proof sketch.*
1. Put $H(x,v)=\sigma_\rho((1-v)F_0(x)+vx)$ for $x\in\Omega$ and $v\in[0,1]$, and $H(x,v)=\infty$ for $x\notin\Omega$.
2. The argument of $\sigma_\rho$ stays within $D$ of $x$, so $H=\infty$ unless $|x|<\rho+D$. Hence $H$ is continuous by the same gluing as for $f$, over the open cover $\Omega\times[0,1]$ and $(S^n\setminus\overline B(0,\rho+D))\times[0,1]$, and $H(\infty,v)=\infty$.
3. $H_0=f$, and $H_1=\sigma_\rho$ because $\sigma_\rho=\infty$ off $B(0,\rho)\subseteq\Omega$.
4. Compose with the homotopy from the pinch to the identity.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the degree of $f$, displays (8.5)-(8.6))

## Depends on

- [The test map](test-map.md)

## Proof depends on

- [The averaged map is continuous](averaged-map-continuous.md)
- [The averaged map moves points little](averaged-map-displacement.md)
- [The pinch is continuous](pinch-continuous.md)
- [The pinch is homotopic to the identity](pinch-homotopy.md)
