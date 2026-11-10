---
article_id: af_b73ccdcd714c3691304bc0c6
declaration: lemma
origin: background
---

# Pushforward of products

Let $C$ be a complex in $\operatorname{Kar}\mathcal B$ and $E$ a complex in $C_\mathbb Z(\mathbb Q)$, each with all but finitely many chain objects zero objects, let $\phi\in M(C)_m$ and $\theta\in M(E)_n$, and let $\phi\otimes\theta$ be their [external product](external-product.md), with block signs $s(p,q)=(-1)^{q(p+m)}$. For chain maps $f:C\to C'$ and $g:E\to E'$, $(f\otimes g)_\%(\phi\otimes\theta)=f_\%\phi\otimes g_\%\theta$, with $f\otimes g$ as in [Tensor product of complexes over the line](complex-product.md).

*Proof sketch.* $f\otimes g$ is block diagonal with no signs, so on each block both sides are $s(p,q)\,f\phi_pf^*\boxtimes g\theta_qg^*$, using functoriality of $\boxtimes$ and naturality of $\kappa$ ([Duals of box products](box-dual.md)).

## Sources

- New: direct from the definitions, in the conventions of [Pushforward of structures](../../base/complexes/structure-push.md).

## Depends on

- [External product of structures](external-product.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)

## Proof depends on

- [Box product with a bounded vector space](box-product.md)
- [Duals of box products](box-dual.md)
