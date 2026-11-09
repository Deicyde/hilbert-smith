---
declaration: lemma
origin: bridged
---
# Adjoint homotopies

Let $a=a_g$, $a'=a_{-g}$ and $S=B_{-g,g}$, so that $a'a-1=dS+Sd$. On $D_i^{N-*}$ (degree $r$ means $D_{N-r}^*$), set $K_r=(-1)^rS^*_{N-r-1}$ and $V_g=a\varphi_iK+U_ga'^*$. Then $dV_g+V_g\delta=a_g\varphi_i-\varphi_ia_{-g}^*$. Eventually $V_g^{[v,v']}$ has graph type $\chi_i(g)$, with bound $\to0$.

*Proof sketch.* Dualizing gives $a^*a'^*-1=S^*d^*+d^*S^*$. With $\delta_r=(-1)^rd^*$ the sign $(-1)^r$ gives $\delta K+K\delta=1-a^*a'^*$. Since $\varphi_i$ and $a$ are chain maps, $d(a\varphi K)+a\varphi K\delta=a\varphi-a\varphi a^*a'^*$. Also $d(Ua'^*)+Ua'^*\delta=(a\varphi a^*-\varphi)a'^*$, and the sum telescopes. For the type: $K,\varphi_i,U_g$ have type $\chi_i(0)$, $a$ has type $\chi_i(g)$, and $a'^*$ has type $\chi_i(-g)^{-1}=\chi_i(g)$. Compose using [buffered restriction](buffered-restriction.md) (3).

## Sources
- HS paper, Section 9; signs rechecked.
## Depends on
- [Product homotopies](product-homotopies.md), [isometry homotopies](isometry-homotopies.md)
## Proof depends on
- [Buffered restriction](buffered-restriction.md), [graph-type matrices](../corner/graph-type.md)
