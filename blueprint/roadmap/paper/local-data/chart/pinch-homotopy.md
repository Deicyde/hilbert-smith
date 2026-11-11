---
article_id: af_59b41e87b71c00d9039dc5a5
declaration: lemma
origin: bridged
---

# The pinch is homotopic to the identity

For $\rho>0$, $\sigma_\rho$ is homotopic to $\mathrm{id}_{S^n}$ relative to $\{\infty\}$.

*Proof sketch.*
1. Let $c_t=(1-t)+t\rho$ for $t\in[0,1]$, and set $G(x,t)=x/(c_t-t|x|)$ where $x\in\mathbb R^n$ and $t|x|<c_t$, with $G(x,t)=\infty$ elsewhere. Then $G_0=\mathrm{id}$, $G_1=\sigma_\rho$, and $G(\infty,t)=\infty$ for every $t$.
2. Continuity on the open set where $t|x|<c_t$ is clear. At the blow-up locus $c_t-t|x|\to0$ while $|x|$ stays near a positive value, so $|G|\to\infty$. At $\infty$, $|G(x,t)|\ge|x|/c_t\ge|x|/\max(1,\rho)$ wherever $G$ is finite.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)
- New: the explicit homotopy $x/((1-t)+t\rho-t|x|)$

## Depends on

- [The pinch map](pinch.md)

## Proof depends on

- [The pinch is continuous](pinch-continuous.md)
