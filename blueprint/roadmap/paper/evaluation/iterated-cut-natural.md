---
declaration: lemma
origin: bridged
---
# Cuts commute with forgetting

Let $U:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$ be induced by $\mathrm{pr}_*\circ U$, and let $U_T:\mathcal A_{\mathbf G}(T)\to\mathcal V_{\mathbf 1}$ forget the group and the labels. Then $U_{T*}\Delta_T=\Delta_{\mathbf 1}U_*$.

*Proof sketch.* [Inner-cut naturality](inner-cut-natural.md) at each step. In the projection, every square commutes strictly up to unitary isomorphism ([A11](../l-theory/A11.md), [D2](../l-theory/D2.md)). At the end, $\Phi\circ U=U_T$ after the identification $T\times\{y_+\}\cong T$.

## Sources
- HS paper, Section 12, display (12.2).
## Depends on
- [Iterated cut](../corner/iterated-cut.md), [forgetting the group](../categories/forget-group.md)
## Proof depends on
- [Inner-cut naturality](inner-cut-natural.md), [D2](../l-theory/D2.md)
