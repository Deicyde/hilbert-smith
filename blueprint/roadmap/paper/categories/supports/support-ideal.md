---
article_id: af_d4da18b4e8d9b6c3495b8ca4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.factorsThrough_supp_iff
---

# Support ideal

Let the $C_p$-action on $X$ be isometric and let $S\subset X$ be invariant. A morphism $[u]:M\to N$ of $\mathcal A_{\mathbf G}(X)$, with representative $u$, factors through an object of $\mathcal A_S$ if and only if, for every $\varepsilon>0$, eventually both endpoint labels of every nonzero entry of $u_i$ lie in the $\varepsilon$-thickening of $S$. (Here $c+y$ lies in the $\varepsilon$-thickening of $S$ if and only if $y$ does, for $c\in C_p$: [translates and thickenings](thickening-invariant.md).)

*Proof sketch.* (⇒) Write $u_i=w_iv_i$ eventually, through $W\in\mathcal A_S$. A nonzero entry passes through a basis element $c$ of $W$, so each endpoint is within $\operatorname{prop}+d(\lambda_W(c),S)$ of $S$ (the entries of $w_i$ and $v_i$ through $c$ are nonzero, so each endpoint is within the propagation of its factor of $\lambda_W(c)$). (⇐) The columns carrying nonzero entries form an invariant sub-basis, by equivariance. Restricting the source to the indices $k$ of its nonzero columns gives an object of $\mathcal A_S$ (its labels are translates of entry labels, and $S$ is invariant), through which $u$ factors by an inclusion and a projection of propagation $0$.

## Sources

- HS paper, Section 2

## Depends on

- [Support subcategory](support-subcategory.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Restriction to a sub-basis](../asymptotic/restriction/restriction-sub-basis.md)
- [Coordinate projection onto a restriction](../asymptotic/restriction/coordinate-projection.md)
- [Inclusion after projection](../asymptotic/restriction/projection-inclusion.md)
- [Factorization through a diagonal projection, columns](../asymptotic/restriction/diagonal-projection-columns.md)
- [Enumerated indices satisfy the predicate](../asymptotic/restriction/restriction-index-mem.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Free category of a finite group](../asymptotic/free-category.md)
- [Propagation](../asymptotic/propagation.md)
- [Translates and thickenings of an invariant set](thickening-invariant.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
