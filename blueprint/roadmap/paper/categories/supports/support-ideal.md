---
article_id: af_d4da18b4e8d9b6c3495b8ca4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.factorsThrough_supp_iff
---

# Support ideal

Let the $C_p$-action on $X$ be isometric and let $S\subset X$ be invariant. A morphism $[u]:M\to N$ of $\mathcal A_{\mathbf G}(X)$, with representative $u$, factors through an object of $\mathcal A_S$ if and only if, for every $\varepsilon>0$, eventually both endpoint labels of every nonzero entry of $u_i$ lie in the $\varepsilon$-thickening of $S$.

*Proof sketch.* (⇒) Write $u_i=w_iv_i$ eventually, through $W\in\mathcal A_S$. A nonzero entry passes through a basis element $c$ of $W$, so each endpoint is within $\operatorname{prop}+d(\lambda_W(c),S)$ of $S$ ([propagation of a product](../asymptotic/prop-mul.md)). (⇐) The columns carrying nonzero entries form an invariant sub-basis, by equivariance. Restricting the source to the indices $k$ of its nonzero columns gives an object of $\mathcal A_S$ (its labels are translates of entry labels, and $S$ is invariant), through which $u$ factors by an inclusion and a projection of propagation $0$.

## Sources

- HS paper, Section 2

## Depends on

- [Support subcategory](support-subcategory.md)

## Proof depends on

- [Propagation of a product](../asymptotic/prop-mul.md)
