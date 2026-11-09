---
declaration: lemma
origin: bridged
---

# Support ideal

A morphism $[u]:M\to N$ factors through an object of $\mathcal A_S$ if and only if, for every $\varepsilon>0$, eventually both endpoint labels of every nonzero entry of $u_i$ lie in the $\varepsilon$-thickening of $S$.

*Proof sketch.* (⇒) Write $u_i=w_iv_i$ eventually, through $W\in\mathcal A_S$. A nonzero entry passes through a basis element $c$ of $W$, so each endpoint is within $\operatorname{prop}+d(\ell_W(c),S)$ of $S$ ([propagation bounds](propagation-bounds.md)). (⇐) The columns and rows carrying nonzero entries form invariant sub-bases. Restricting the source to its nonzero columns gives an object of $\mathcal A_S$, through which $u$ factors by an inclusion and a projection of propagation $0$.

## Sources

- HS paper, Section 2

## Depends on

- [Support subcategory](support-subcategory.md)

## Proof depends on

- [Propagation bounds](propagation-bounds.md)
