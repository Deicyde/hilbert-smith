---
article_id: af_ee2a09f748fee4a426c5056d
declaration: lemma
origin: bridged
---
# The cut boundary from the inner side

Let $A,B,Z\subseteq X$ be data as in the [cut boundary](../categories/cuts/cut-boundary.md): closed and invariant, $Z\subseteq A$, $Z\cap B=\varnothing$, with $S=A\cup B$ and $Y=A\cap B$. Let $q_Z:\mathcal A_S\to\mathcal A_S/\mathcal A_Z$ be the quotient functor, and let $\partial_{B,A}:\mathbb L_k(\mathcal A_S)\to\mathbb L_{k-1}(\mathcal A_Y)$ be the [excision boundary](../l-theory/ultimate/boundary/excision-boundary.md) of the [support excisive pair](../categories/supports/support-excisive-pair.md) $(\mathcal A_B,\mathcal A_A)$ in $\mathcal A_S$. Then for every $x\in\mathbb L_k(\mathcal A_S)$,
$$\partial_{A,B}\big((q_Z)_*x\big)=-\,\partial_{B,A}\,x .$$

*Proof sketch.*
1. $q_Z$ is a strict duality functor that is the identity on objects, so it carries $\mathcal A_A$ and $\mathcal A_B$ into the predicates $\mathcal U_A$ and $\mathcal U_B$ of the [cut square](../categories/cuts/cut-square.md). [Naturality of the excision boundary](../l-theory/ultimate/boundary/excision-boundary-naturality.md), from the support excisive pair $(\mathcal A_A,\mathcal A_B)$ in $\mathcal A_S$ to the cut square, gives $\partial^{\rm exc}_{A,B}(q_Z)_*x=(q_Z|_{\mathcal A_Y})_*\,\partial'_{A,B}x$, where $\partial'_{A,B}$ is the excision boundary of $(\mathcal A_A,\mathcal A_B)$.
2. $q_Z|_{\mathcal A_Y}$ is the functor $\mathcal A_Y\to\mathcal U_Y$ of [separated support](../categories/supports/quotient-separation-iso.md) ($Y\cap Z=\varnothing$), whose inverse is the $\sigma$ in the definition of $\partial_{A,B}$. By [functoriality](../l-theory/ultimate/groups/induced-map-comp.md), $\partial_{A,B}(q_Z)_*x=\sigma_*(q_Z|_{\mathcal A_Y})_*\partial'_{A,B}x=\partial'_{A,B}x$.
3. The [two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md), for the support excisive pairs $(\mathcal A_A,\mathcal A_B)$ and $(\mathcal A_B,\mathcal A_A)$ with the common intersection $\mathcal A_Y$, give $\partial'_{A,B}x=-\partial_{B,A}x$.

**Remark (not formalized).** $\partial_{B,A}=\partial\circ r_*\circ(q_A)_*$ quotients by the side $A$ that contains the exterior, inverts the excision equivalence $\mathcal A_B/\mathcal A_Y\to\mathcal A_S/\mathcal A_A$, and takes the boundary of $\mathcal A_Y\subseteq\mathcal A_B$. In the evaluation chapter the side $B$ is always a grid box or a face tensored with $\mathbb{CP}^2$, which has an exact duality, so this is the side on which the [inner cut formula](inner-cut-formula.md) computes.

## Sources
- HS paper, Section 6.
- New: the cut boundary is computed from the side that does not contain the exterior, at the cost of a sign.
## Depends on
- [Cut boundary](../categories/cuts/cut-boundary.md), [support excisive pair](../categories/supports/support-excisive-pair.md), [excision boundary](../l-theory/ultimate/boundary/excision-boundary.md), [induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
## Proof depends on
- [Cut square](../categories/cuts/cut-square.md), [naturality of the excision boundary](../l-theory/ultimate/boundary/excision-boundary-naturality.md), [separated support in a quotient](../categories/supports/quotient-separation-iso.md), [functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md), [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md)
