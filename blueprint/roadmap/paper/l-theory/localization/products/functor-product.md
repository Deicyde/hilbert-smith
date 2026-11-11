---
article_id: af_beb766bf982714e165201f8b
declaration: lemma
origin: background
---

# Duality functors commute with products

Let $(F,\xi):\mathcal A\to\mathcal A'$ be a duality functor, $j\ge0$, $G=C_{\mathbb Z^j}F$ and $G'=C_{\mathbb Z^{j+1}}F$ its [bounded extensions](../../bounded/categories/bounded-functor.md), with $\xi$ applied entrywise. On objects and complexes of the idempotent completions, $G$ and $G'$ act through their [completions](../../base/categories/karoubi-functor.md) $\mathrm{Kar}\,G$ and $\mathrm{Kar}\,G'$, with duality data $\xi^G_{(M,e)}=\xi_M\circ F(e^*)$ entrywise; we write $G$, $G'$ for these. Let $C$ be a complex in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$ and $E$ a complex in $C_\mathbb Z(\mathbb Q)$, each with finitely many nonzero chain objects, and let $\phi\in M(C)_m$ and $\theta\in M(E)_n$. Then there is an isomorphism of complexes $\omega:G'(C\otimes E)\to GC\otimes E$ of propagation $0$ with
$$\omega_\%\big(G'_\%(\phi\otimes\theta)\big)=G_\%\phi\otimes\theta.$$

*Proof sketch.*
1. Objects. For $N=(M,e)$ in $\operatorname{Kar}C_{\mathbb Z^j}\mathcal A$ and $V$ in $C_\mathbb Z(\mathbb Q)$, the canonical isomorphisms $F(M^{\oplus d})\cong F(M)^{\oplus d}$ of the additive functor $F$ form an isomorphism $\omega_{N,V}:G'(N\boxtimes V)\cong G(N)\boxtimes V$ of propagation $0$ ([Box product with a bounded vector space](box-product.md)). It is natural in both variables: $F$ is $\mathbb Q$-linear and the entries of maps of $C_\mathbb Z(\mathbb Q)$ are rational numbers.
2. Duality data. With $\kappa$ of [Duals of box products](box-dual.md),
$$\omega_{N,V}^{*}\circ\kappa^{-1}_{GN,V}\circ(\xi^G_N\boxtimes1_{V^*})\circ\omega_{N^*,V^*}=\xi^{G'}_{N\boxtimes V}\circ G'(\kappa^{-1}_{N,V})$$
as maps $G'(N^*\boxtimes V^*)\to G'(N\boxtimes V)^*$. Both sides are block diagonal in the summands $M^*$, with block $\xi_M\circ F(e^*)$: on the right because $\xi$ is natural, so it commutes with the inclusions and projections of the biproduct $M^{\oplus d}$; on the left by the definitions of $\omega$ and $\kappa$.
3. Complexes. The maps $\omega_{C_p,E_q}$ form an isomorphism of complexes $\omega:G'(C\otimes E)\to GC\otimes E$ ([Tensor product of complexes](complex-product.md)), by naturality in both variables.
4. Structures. The block of $G'_\%(\phi\otimes\theta)$ at $(p,q)$ is $G'(s\,\phi_p\boxtimes\theta_q)\circ(\xi^{G'})^{-1}$ and that of $G_\%\phi\otimes\theta$ is $s\,(G(\phi_p)\circ(\xi^G)^{-1})\boxtimes\theta_q$, with the same sign $s=(-1)^{q(p+m)}$ of the [external product](external-product.md). Step 2, the naturality of $\omega$ and of $\kappa$ identify them under $\omega$.

## Sources

- New: the comparison isomorphism, built from $\xi$.

## Depends on

- [Bounded extension of a duality functor](../../bounded/categories/bounded-functor.md)
- [Duality functor](../../base/categories/duality-functor.md)
- [Tensor product of complexes](complex-product.md)
- [External product of structures](external-product.md)
- [Pushforward of structures](../../base/complexes/structure-push.md)
- [Completion of a duality functor](../../base/categories/karoubi-functor.md)

## Proof depends on

- [Box product with a bounded vector space](box-product.md)
- [Duals of box products](box-dual.md)
- [Tensor product of complexes](complex-product.md)
