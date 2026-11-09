---
article_id: af_e56146d0e7e9cd80a11ea99d
declaration: lemma
origin: background
---

# Product formulas

Let $C$ be a complex in $\operatorname{Kar}\mathcal B$ and $E$ a complex in $C_\mathbb Z(\mathbb Q)$, as in [External product with a complex over the line](external-product.md). Let $\phi\in M(C)_m$, $\theta\in M(E)_n$, $N=m+n$, and $s(p,q)=(-1)^{q(p+m)}$.
1. $\partial(\phi\otimes\theta)=\partial\phi\otimes\theta+(-1)^m\,\phi\otimes\partial\theta$.
2. $T(\phi\otimes\theta)=T\phi\otimes T\theta$.
3. For chain maps $f:C\to C'$ and $g:E\to E'$, $(f\otimes g)_\%(\phi\otimes\theta)=f_\%\phi\otimes g_\%\theta$.
4. The map $\Xi:(C\otimes E)^{N-*}\to C^{m-*}\otimes E^{n-*}$ equal to $s(a,b)$ times $\kappa$ on the summand $(C_{m-a}\boxtimes E_{n-b})^*$, which it carries to $C^*_{m-a}\boxtimes E^*_{n-b}$ in position $(a,b)$, is an isomorphism of complexes. If $\partial\phi=0$ and $\partial\theta=0$, then $(\phi\otimes\theta)_\natural=(\phi_\natural\otimes\theta_\natural)\circ\Xi$.
5. If $f$ and $g$ are chain homotopy equivalences, so is $f\otimes g$.

*Proof sketch.* Index blocks by the target $C_a\boxtimes E_b$.
1. Write $(\partial F)_r=dF_{r+1}+(-1)^rF_rd^*$ for $F=\phi\otimes\theta$. The terms with source $C^*_{m-a-1}\boxtimes E^*_{n-b}$ are $s(a+1,b)\,d\phi_{a+1}\boxtimes\theta_b+(-1)^{a+b}s(a,b)\,\phi_ad^*\boxtimes\theta_b$. Since $s(a+1,b)=(-1)^bs(a,b)$, they sum to $(-1)^bs(a,b)(\partial\phi)_a\boxtimes\theta_b$, and $(-1)^bs(a,b)=(-1)^{b(a+m-1)}$ is the sign of $\partial\phi\otimes\theta$. The terms with source $C^*_{m-a}\boxtimes E^*_{n-b-1}$ are $(-1)^as(a,b+1)\,\phi_a\boxtimes d\theta_{b+1}+(-1)^{a+b}(-1)^{m-a}s(a,b)\,\phi_a\boxtimes\theta_bd^*$; the factor $(-1)^{m-a}$ is the dual of the sign in $(-1)^p1\boxtimes d$. Since $s(a,b+1)=(-1)^{a+m}s(a,b)$, they sum to $(-1)^ms(a,b)\,\phi_a\boxtimes(\partial\theta)_b$.
2. Put $r=a+b$, $\alpha=m-a$, $\beta=n-b$. The $(a,b)$ block of $T(\phi\otimes\theta)$ is $(-1)^{r(N-r)}s(\alpha,\beta)\,\phi_\alpha^*\boxtimes\theta_\beta^*$, with exponent $\equiv a\alpha+a\beta+b\alpha+b\beta+\beta a\equiv a\alpha+b\alpha+b\beta$. The block of $T\phi\otimes T\theta$ is $(-1)^{b(a+m)+a\alpha+b\beta}\,\phi_\alpha^*\boxtimes\theta_\beta^*$. The exponents agree, since $b\alpha\equiv bm+ab$.
3. $f\otimes g$ is block diagonal with no signs.
4. In position $(a,b)$, the differential of $(C\otimes E)^{N-*}$ has components $(-1)^{a+b}d^*\boxtimes1$ to $(a-1,b)$ and $(-1)^{b+m}1\boxtimes d^*$ to $(a,b-1)$; that of $C^{m-*}\otimes E^{n-*}$ has $(-1)^ad^*\boxtimes1$ and $(-1)^{a+b}1\boxtimes d^*$. The identities $s(a-1,b)=(-1)^bs(a,b)$ and $s(a,b-1)=(-1)^{a+m}s(a,b)$ are exactly the chain-map condition. The factorization is the definition of $\phi\otimes\theta$ read block by block.
5. A homotopy $h:f\simeq f'$ gives $h\otimes g:f\otimes g\simeq f'\otimes g$, and $h':g\simeq g'$ gives $f\otimes g\simeq f\otimes g'$ through $(-1)^pf_p\boxtimes h'_q$. Apply this to the composites with homotopy inverses, using $(f'\otimes g')(f\otimes g)=f'f\otimes g'g$.

## Sources

- [Ranicki 1980 I, §8, products of symmetric structures](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the block computations, in the conventions of [Structure complex](../../base/complexes/structure-complex.md), [The involution T](../../base/complexes/structure-involution.md) and [Dual complex](../../base/complexes/dual-complex.md).

## Depends on

- [External product with a complex over the line](external-product.md)
- [The involution T](../../base/complexes/structure-involution.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Duality map of a cycle](../../base/complexes/cycle-chain-map.md)

## Proof depends on

- [External product with a complex over the line](external-product.md)
