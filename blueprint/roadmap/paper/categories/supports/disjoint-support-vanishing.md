---
article_id: af_6c1d86c8a9e021d63b736a87
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.mkHom_eq_zero_of_disjoint
---

# Maps through a disjoint support vanish

Let $X$ be compact with an isometric $C_p$-action, and let $S,Z\subset X$ be disjoint, closed and invariant. A morphism $[u]:M\to N$ of $\mathcal A_{\mathbf G}(X)$ into an $S$-supported object $N$ that factors through an object of $\mathcal A_Z$ is zero.

*Proof sketch.* Disjoint compact and closed sets have disjoint $\delta$-thickenings for some $\delta>0$. By the [support ideal](support-ideal.md), eventually the row label of every nonzero entry of $u_i$ is $\delta$-close to $Z$; it is also $\delta$-close to $S$, because $N$ is $S$-supported and $S$ is invariant. So eventually $u_i=0$.

## Sources

- HS paper, Section 2
- New: a named step of the support calculus.

## Depends on

- [Support subcategory](support-subcategory.md)
- [Quotient by a subcategory](../../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Support ideal](support-ideal.md)
- [Translates and thickenings of an invariant set](thickening-invariant.md)
- [Maps factoring through a subcategory](../../l-theory/base/categories/filtration-ideal.md)
