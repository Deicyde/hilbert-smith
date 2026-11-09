---
article_id: af_61ff75dda609f4b497e6ce43
declaration: theorem
origin: bridged
---

# Mayer-Vietoris middle exactness

For an excisive pair $(\mathcal U_A,\mathcal U_B)$ in $\mathcal A$ with inclusions $i_A,i_B$, if $x\in\mathbb L_k(\mathcal A)$ and $\partial_{A,B}x=0$, then $x=(i_A)_*a+(i_B)_*b$ for some $a\in\mathbb L_k(\mathcal U_A)$ and $b\in\mathbb L_k(\mathcal U_B)$.

*Proof sketch.*
1. Put $z=r_*(q_B)_*x\in\mathbb L_k(\mathcal U_A/\mathcal U_Y)$. Then $\partial z=\partial_{A,B}x=0$ ([Excision boundary](excision-boundary.md)), so [Ultimate exactness at the quotient](exact-at-quotient.md) for $\mathcal U_Y\subset\mathcal U_A$ gives $a$ with $z=(q_Y)_*a$.
2. By [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md), $e_*r_*=\mathrm{id}$, so $(q_B)_*x=e_*z=e_*(q_Y)_*a=(q_B)_*(i_A)_*a$ by the [excision square](excision-square.md).
3. So $(q_B)_*(x-(i_A)_*a)=0$, and [Ultimate exactness in the middle](exact-in-middle.md) for $\mathcal U_B\subset\mathcal A$ gives $b$ with $x-(i_A)_*a=(i_B)_*b$.

## Sources

- HS paper, Section 4 (Mayer-Vietoris for a closed invariant cover)
- New: group-level argument from the two exactness statements and excision.

## Depends on

- [Excision boundary](excision-boundary.md)
- [Induced map on ultimate L](../groups/induced-map.md)

## Proof depends on

- [Ultimate exactness at the quotient](exact-at-quotient.md)
- [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md)
- [Excision square](excision-square.md)
- [Ultimate exactness in the middle](exact-in-middle.md)
