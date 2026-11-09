---
article_id: af_2168191d71ec9306bc24f5db
declaration: def
origin: background
---

# External product with a complex over the line

Let $\mathcal B$ be a duality category, and let $\mathbb Q$ be the duality category of based vector spaces of [The symmetric line](symmetric-line.md).

*Objects and maps.* For $N=(M,e)$ in $\operatorname{Kar}\mathcal B$ and $V$ in $C_\mathbb Z(\mathbb Q)$ with $V_n=\mathbb Q^{d_n}$, let $N\boxtimes V$ be the object of $\operatorname{Kar}C_\mathbb Z(\mathcal B)$ with $M^{\oplus d_n}$ in position $n$ and idempotent $e$ on each summand. For $f:N\to N'$ and $g:V\to V'$, $(f\boxtimes g)_{mn}$ is the block matrix whose $(i,i')$ entry is $(g_{mn})_{ii'}\,f$. Then $f\boxtimes g$ has the propagation of $g$, $\boxtimes$ is a $\mathbb Q$-bilinear functor, and there is a canonical isomorphism $\kappa:(N\boxtimes V)^*\cong N^*\boxtimes V^*$ with $\kappa(f\boxtimes g)^*\kappa^{-1}=f^*\boxtimes g^*$. When $\mathcal B=C_{\mathbb Z^j}\mathcal A$, the target is $\operatorname{Kar}C_{\mathbb Z^{j+1}}\mathcal A$ and the new coordinate is the outermost one.

*Complexes.* For a complex $C$ in $\operatorname{Kar}\mathcal B$ and a complex $E$ in $C_\mathbb Z(\mathbb Q)$, each with all but finitely many chain objects zero objects, $(C\otimes E)_r=\bigoplus_{p+q=r}C_p\boxtimes E_q$, with differential $d\boxtimes1+(-1)^p\,1\boxtimes d$ on $C_p\boxtimes E_q$. Then $d^2=0$. For chain maps $f:C\to C'$, $g:E\to E'$, the chain map $f\otimes g$ is $f_p\boxtimes g_q$ on $C_p\boxtimes E_q$. If every $E_q$ is supported in a set $S\subset\mathbb Z$ (its positions outside $S$ hold zero objects), so is every $(C\otimes E)_r$.

*Structures.* For $\phi\in M(C)_m$ and $\theta\in M(E)_n$, let $\phi\otimes\theta\in M(C\otimes E)_{m+n}$ have, from the summand $C^*_{m-p}\boxtimes E^*_{n-q}$ of $(C\otimes E)^*_{m+n-p-q}$ (identified through $\kappa$) to $C_p\boxtimes E_q$, the block
$$(-1)^{q(p+m)}\,\phi_p\boxtimes\theta_q,$$
and zero blocks elsewhere.

## Sources

- [Ranicki 1980 I, §8, products](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the sign $(-1)^{q(p+m)}$ is the one for which [Product formulas](product-formulas.md) hold in the conventions of [Structure complex](../../base/complexes/structure-complex.md) and [Dual complex](../../base/complexes/dual-complex.md).

## Depends on

- [Idempotent completion with duality](../../base/categories/karoubi-duality.md)
- [Iterated bounded categories](../../bounded/categories/iterated-bounded-category.md)
- [Structure complex](../../base/complexes/structure-complex.md)
- [The symmetric line](symmetric-line.md)
