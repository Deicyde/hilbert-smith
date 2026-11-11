---
article_id: af_7ac498ab680e0970cc6787d5
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.strProd_T
---

# Products commute with T

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects, let $\phi\in M(C)_m$ and $\theta\in M(E)_n$, and let $\phi\otimes\theta$ be their [external product](external-product.md), with block signs $s(p,q)=(-1)^{q(p+m)}$. Then $T(\phi\otimes\theta)=T\phi\otimes T\theta$.

*Proof sketch.* Put $N=m+n$, $r=a+b$, $\alpha=m-a$, $\beta=n-b$. The $(a,b)$ block of $T(\phi\otimes\theta)$ is $(-1)^{r(N-r)}s(\alpha,\beta)\,\phi_\alpha^*\boxtimes\theta_\beta^*$ (through $\kappa$), with exponent $\equiv a\alpha+a\beta+b\alpha+b\beta+\beta a\equiv a\alpha+b\alpha+b\beta$. The block of $T\phi\otimes T\theta$ is $(-1)^{b(a+m)+a\alpha+b\beta}\,\phi_\alpha^*\boxtimes\theta_\beta^*$. The exponents agree, since $b\alpha\equiv bm+ab$.

## Sources

- [Ranicki 1980 I, §8, products of symmetric structures](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the block computation, in the conventions of [The involution T](../../base/complexes/structure-involution.md).

## Depends on

- [Duality pairings](duality-pairing.md)
- [External product of structures](external-product.md)
- [The involution T](../../base/complexes/structure-involution.md)

## Proof depends on

- [External product of structures](external-product.md)
