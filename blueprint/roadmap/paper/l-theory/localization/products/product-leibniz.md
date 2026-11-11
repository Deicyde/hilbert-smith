---
article_id: af_ae98ff4aff47b3fc8c958f05
declaration: lemma
origin: background
---

# Leibniz rule for products

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](duality-pairing.md), $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects, let $\phi\in M(C)_m$ and $\theta\in M(E)_n$, and let $\phi\otimes\theta$ be their [external product](external-product.md), with block signs $s(p,q)=(-1)^{q(p+m)}$. Then
$$\partial(\phi\otimes\theta)=\partial\phi\otimes\theta+(-1)^m\,\phi\otimes\partial\theta.$$

*Proof sketch.* Index blocks by the target $C_a\boxtimes E_b$ and write $(\partial F)_r=dF_{r+1}+(-1)^rF_rd^*$ for $F=\phi\otimes\theta$.
1. The terms with source $C^*_{m-a-1}\boxtimes E^*_{n-b}$ are $s(a+1,b)\,d\phi_{a+1}\boxtimes\theta_b+(-1)^{a+b}s(a,b)\,\phi_ad^*\boxtimes\theta_b$. Since $s(a+1,b)=(-1)^bs(a,b)$, they sum to $(-1)^bs(a,b)(\partial\phi)_a\boxtimes\theta_b$, and $(-1)^bs(a,b)=(-1)^{b(a+m-1)}$ is the sign of $\partial\phi\otimes\theta$.
2. The terms with source $C^*_{m-a}\boxtimes E^*_{n-b-1}$ are $(-1)^as(a,b+1)\,\phi_a\boxtimes d\theta_{b+1}+(-1)^{a+b}(-1)^{m-a}s(a,b)\,\phi_a\boxtimes\theta_bd^*$; the factor $(-1)^{m-a}$ is the dual of the sign in $(-1)^p1\boxtimes d$. Since $s(a,b+1)=(-1)^{a+m}s(a,b)$, they sum to $(-1)^ms(a,b)\,\phi_a\boxtimes(\partial\theta)_b$.

## Sources

- [Ranicki 1980 I, §8, products of symmetric structures](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the block computation, in the conventions of [Structure complex](../../base/complexes/structure-complex.md) and [Dual complex](../../base/complexes/dual-complex.md).

## Depends on

- [Duality pairings](duality-pairing.md)
- [External product of structures](external-product.md)
- [Structure complex](../../base/complexes/structure-complex.md)

## Proof depends on

- [External product of structures](external-product.md)
