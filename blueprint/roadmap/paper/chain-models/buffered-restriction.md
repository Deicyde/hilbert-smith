---
declaration: lemma
origin: bridged
---
# Buffered restriction

1. If $b\in\mathcal B_i(v)$, then $\tilde x_b\in U^+\subseteq Z^+$.
2. For $0<v<v'$ there is $\eta>0$ such that every matrix $u$ with sphere propagation less than $\eta$ satisfies $u\iota_v=\iota_{v'}u^{[v,v']}$.
3. If $u\iota_v=\iota_{v'}u^{[v,v']}$, then $(u'u)^{[v,v'']}=u'^{[v',v'']}u^{[v,v']}$.

*Proof sketch.* (1) [Preimages](../local-data/chart/test-map-proper.md) with $C=\overline B(0,v)$. (2) $d_S$ and the Euclidean metric are uniformly equivalent on $\overline B(0,v')$, and $\overline B(0,v)$ has positive $d_S$-distance from the complement of $B(0,v')$. (3) Matrix algebra.

## Sources
- HS paper, Section 9 ("target labels are defined eventually").
## Depends on
- [Control labels](control-labels.md)
