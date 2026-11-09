---
article_id: af_f96307d7cc5ca74543b5e359
declaration: lemma
origin: bridged
---

# Naturality of the excision boundary

Let $(\mathcal U_A,\mathcal U_B)$ and $(\mathcal U'_A,\mathcal U'_B)$ be excisive pairs in $\mathcal A$ and $\mathcal A'$, and $F:\mathcal A\to\mathcal A'$ a duality functor with $F(\mathcal U_A)\subset\mathcal U'_A$ and $F(\mathcal U_B)\subset\mathcal U'_B$, so that $F(\mathcal U_Y)\subset\mathcal U'_Y$. Then $\partial'_{A,B}\circ F_*=(F|_{\mathcal U_Y})_*\circ\partial_{A,B}:\mathbb L_k(\mathcal A)\to\mathbb L_{k-1}(\mathcal U'_Y)$.

*Proof sketch.* Let $\bar F_B:\mathcal A/\mathcal U_B\to\mathcal A'/\mathcal U'_B$ and $\bar F_{AY}:\mathcal U_A/\mathcal U_Y\to\mathcal U'_A/\mathcal U'_Y$ be the induced functors. Applying $F$ entrywise to classes gives the equalities of duality functors $q'_B\circ F=\bar F_B\circ q_B$ and $e'\circ\bar F_{AY}=\bar F_B\circ e$.
1. By [Functoriality on ultimate L](../groups/induced-map-comp.md), $r'_*(q'_B)_*F_*=r'_*(\bar F_B)_*(q_B)_*$.
2. By [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md), $e_*r_*=\mathrm{id}$ and $r'_*e'_*=\mathrm{id}$. With functoriality, $r'_*(\bar F_B)_*=r'_*(\bar F_B)_*e_*r_*=r'_*e'_*(\bar F_{AY})_*r_*=(\bar F_{AY})_*r_*$.
3. [Naturality of the ultimate boundary](ultimate-boundary-naturality.md) for $F|_{\mathcal U_A}:\mathcal U_A\to\mathcal U'_A$ gives $\partial'(\bar F_{AY})_*=(F|_{\mathcal U_Y})_*\partial$.
Composing 1-3 with the definition of the [excision boundary](excision-boundary.md) gives the claim.

## Sources

- HS paper, Section 6 (naturality for duality-preserving functors preserving the support categories)

## Depends on

- [Excision boundary](excision-boundary.md)

## Proof depends on

- [Functoriality on ultimate L](../groups/induced-map-comp.md)
- [Equivalence invariance on ultimate L](../groups/equivalence-invariance.md)
- [Naturality of the ultimate boundary](ultimate-boundary-naturality.md)
