---
article_id: af_32afbe8d967492e8b6f3b2e7
declaration: lemma
origin: bridged
---

# Excision boundary of a preimage

For an excisive pair $(\mathcal U_A,\mathcal U_B)$ in $\mathcal A$, if $y\in\mathbb L_k(\mathcal A)$ and $z\in\mathbb L_k(\mathcal U_A/\mathcal U_Y)$ satisfy $(q_B)_*y=e_*z$, then $\partial_{A,B}\,y=\partial z$, where $\partial$ is the ultimate boundary of $\mathcal U_Y\subset\mathcal U_A$.

*Proof sketch.* [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md), applied to $e$ and $r$, gives $r_*e_*=\mathrm{id}$. So $r_*(q_B)_*y=r_*e_*z=z$, and $\partial_{A,B}y=\partial z$ by the definition of the [excision boundary](excision-boundary.md).

## Sources

- HS paper, Section 6

## Depends on

- [Excision boundary](excision-boundary.md)

## Proof depends on

- [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md)
