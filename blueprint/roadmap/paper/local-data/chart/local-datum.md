---
article_id: af_e875b151a685860f7cc015e7
declaration: structure
origin: bridged
statement: formalized
lean: HSP.LocalDatum
---

# Local datum

Let $p$ be a prime, $n\in\mathbb N$, $0<D\le 1/64$ and $0<\rho_+<1/4$. A local datum with constants $(D,\rho_+)$ in dimension $n$ consists of:

- an open set $\Omega\subseteq\mathbb R^n$ (Euclidean norm $|\cdot|$);
- a jointly continuous action $(a,x)\mapsto a\cdot x$ of $\mathbb Z_p$ on $\Omega$;

subject to three conditions (the bounds on $D$ and $\rho_+$ are part of the datum):

- containment: $B(0,2)\subseteq\Omega$;
- displacement: $|a\cdot x-x|\le D$ for all $a\in\mathbb Z_p$ and $x\in\Omega$;
- no fixed points near the origin: for each $x\in\Omega$ with $|x|\le\rho_+$ there is $a\in\mathbb Z_p$ with $a\cdot x\ne x$.

The last condition does not make stabilizers trivial; it only excludes points fixed by all of $\mathbb Z_p$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (the chart and small subgroup of display (8.1), moved onto the saturated open set, with the small subgroup renamed $\mathbb Z_p$)

## Depends on
