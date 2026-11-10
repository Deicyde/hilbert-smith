---
article_id: af_c41244647849bb94361f41c3
declaration: lemma
origin: cited
---

# The truncated line is a pair

Let $x=(C,\phi)$ be a strict $m$-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,D$, and let $\kappa_m=\pm1$ be the boundary sign that [Product with a pair](../localization/products/product-with-pair.md) gives for an $m$-dimensional complex and a $1$-dimensional pair. Then the product of $x$ with the ray pair $(f:\mathrm{pt}_0\to\Lambda_+,\delta\phi_0,\theta)$ of [The endpoint of the ray](ray-endpoint.md) and [The symmetric ray](symmetric-ray.md) is a strict $(m+1)$-dimensional symmetric Poincaré pair $(1\otimes f:x\otimes\mathrm{pt}_0\to x\otimes\Lambda_+)$ in $\mathrm{Kar}\,H_+$. Its boundary is a strict $m$-dimensional symmetric Poincaré complex in $\mathrm{Kar}\,H_b$ whose class in $L^p_m(H_b)$ is $\varepsilon_m\,\iota_{0*}[C,\phi]$, where $\varepsilon_m=\sigma_0\kappa_m=-\kappa_m$.

*Proof sketch.*
1. The ray pair: structure. $\delta\phi_0$ is symmetric: for $n=1$ the involution is $(T g)_r=g_{1-r}^*$, and the coefficient of $e_{k+1/2}$ in $\delta\phi_0(v_n^*)$ equals that of $v_n$ in $\delta\phi_0(e_{k+1/2}^*)$, including $\tfrac12$ for $v_0^*\mapsto e_{1/2}$ and $e_{1/2}^*\mapsto v_0$. The only component of $\partial\delta\phi_0$ is $d(\delta\phi_0)_1+(\delta\phi_0)_0d^*$ on $\Lambda_{+,0}^*$. At $v_n^*$ with $n\ge1$ it vanishes as on the line. At $v_0^*$: $d(\tfrac12e_{1/2})=\tfrac12(v_1-v_0)$, and $d^*v_0^*=-e_{1/2}^*$ because $e_{-1/2}$ is absent, with $\delta\phi_0(-e_{1/2}^*)=-\tfrac12(v_0+v_1)$. The sum is $-v_0=f\theta f^*(v_0^*)$, since $\sigma_0=-1$. So $\partial\delta\phi_0=f_\%\theta$. The boundary $(\mathrm{pt}_0,\theta)$ is Poincaré, as $\theta_\natural=-1$.
2. The ray pair: duality. The projection $\mathcal C(f)\to\Lambda_+/\mathbb Qv_0$ is an equivalence, since $f$ is a split injection. The cellular map $v_n^*\mapsto e_{n+1/2}$, $e_{n+1/2}^*\mapsto v_{n+1}$ is an isomorphism $\Lambda_+^{1-*}\to\Lambda_+/\mathbb Qv_0$ of propagation $1$. The homotopy of [The line is Poincaré](../localization/products/symmetric-line-poincare.md), restricted to $n\ge0$, makes the projected pair map homotopic to it. So the pair map is an equivalence by two-out-of-three, and the ray pair is a strict $1$-dimensional Poincaré pair.
3. Product. [Product with a pair](../localization/products/product-with-pair.md) makes $(1\otimes f:x\otimes\mathrm{pt}_0\to x\otimes\Lambda_+)$ a strict $(m+1)$-dimensional Poincaré pair in $\mathrm{Kar}\,C_\mathbb Z(D)$ with boundary structure $\kappa_m\,\phi\otimes\theta$.
4. Supports. The chain objects of $x\otimes\Lambda_+$ are zero objects at positions $n<0$, and those of $x\otimes\mathrm{pt}_0$ at positions $n\ne0$. $\mathrm{Kar}\,H_+$ is the full subcategory of $\mathrm{Kar}\,C_\mathbb Z(D)$ on the objects $(M,e)$ with $M\in H_+$, closed under sums and duals, so every datum of the pair, including the homotopy inverses and homotopies, lies in it; likewise the boundary lies in $\mathrm{Kar}\,H_b$.
5. Class. The isomorphism $C_r\otimes\mathbb Qv_0\cong C_r$ at position $0$ is an isomorphism $u:\iota_0C\to x\otimes\mathrm{pt}_0$ of propagation $0$ with $u_\%(\sigma_0\kappa_m\,\iota_{0\%}\phi)=\kappa_m\,\phi\otimes\theta$. By [Homotopy-isometry invariance](../base/groups/homotopy-isometry-invariance.md) with $\chi=0$, the boundary has class $[\iota_0C,\varepsilon_m\iota_{0\%}\phi]$, which is $\varepsilon_m\iota_{0*}[C,\phi]$ by the definition of the [induced homomorphism](../base/groups/induced-map.md) and [Negation in L^p](../base/groups/l-group-neg.md).

## Sources

- [Ranicki 1980 I, §8, products of complexes and pairs](../../../../sources/paper/ranicki-1980.md) [U]
- [Ranicki 1992, §16](../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [The symmetric ray](symmetric-ray.md)
- [The endpoint of the ray](ray-endpoint.md)
- [Product with a pair](../localization/products/product-with-pair.md)
- [Strict Poincaré pair](../base/pairs/poincare-pair.md)
- [Degree-zero inclusion](../bounded/half-lines/degree-zero-inclusion.md)
- [Half-line subcategories](../bounded/half-lines/half-lines.md)
- [Induced homomorphism](../base/groups/induced-map.md)

## Proof depends on

- [Structure complex](../base/complexes/structure-complex.md)
- [The involution T](../base/complexes/structure-involution.md)
- [Pair map](../base/pairs/pair-map.md)
- [The line is Poincaré](../localization/products/symmetric-line-poincare.md)
- [Product with a pair](../localization/products/product-with-pair.md)
- [Homotopy-isometry invariance](../base/groups/homotopy-isometry-invariance.md)
- [Negation in L^p](../base/groups/l-group-neg.md)
