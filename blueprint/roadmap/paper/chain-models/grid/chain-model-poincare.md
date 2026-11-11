---
article_id: af_d954bb703e948a36e303def2
declaration: theorem
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModel_poincare
---
# The chain model is Poincaré

For every $i$, with $d$ the differential of $D_i$ and of $D_i^{N-*}$ (on the latter $d_r=(-1)^rd^*$):
1. $\partial\varphi_i=0$ and $T\varphi_i=\varphi_i$;
2. $b_i$ is a chain map, and it is the exact inverse of $(\varphi_i^{u})_\natural$, where $\varphi_i^u=(\cdots(\varphi\otimes\varphi)\otimes\cdots\otimes\varphi)\otimes\varphi_P$ is the same product of the unsymmetrized circle structures. With $A=\varphi^sb$ and $A'=b\varphi^s$,
$$H_i=\sum_{j=1}^n1^{\otimes(j-1)}\otimes K\otimes A^{\otimes(n-j)}\otimes1_P,\qquad H'_i=\Xi^{-1}\Bigl(\sum_{j=1}^n1^{\otimes(j-1)}\otimes K'\otimes A'^{\otimes(n-j)}\otimes1_{P^{4-*}}\Bigr)\Xi$$
satisfy $\varphi_ib_i-1=dH_i+H_id$ and $b_i\varphi_i-1=dH'_i+H'_id$. Tensors of maps carry the sign $(f\otimes g)(x\otimes y)=(-1)^{|g||x|}f(x)\otimes g(y)$, and are computed in the explicit bases of the [tensor product of based complexes](based-complex-tensor.md); the sums are formed by the telescoping recursion $H^{(j+1)}=H^{(j)}\otimes A+1\otimes K$ from $H^{(0)}=0$ on the unit complex, $H_i=H^{(n)}\otimes1_P$, and likewise for $H'_i$ through $\Xi$;
3. with cells labelled at their centers, $\varphi_i,b_i,H_i,H'_i$ have $d_\infty$-propagation at most $h_i$;
4. $\varepsilon\varphi_i(\alpha)=\alpha(z_i)$ for every $\alpha\in D_N^*$, the degree-$0$ part of $D_i^{N-*}$, where $\varepsilon=\varepsilon^{\otimes n}\otimes\varepsilon_P$ on $(D_i)_0=C(k_i)_0\otimes P_0$.

*Proof sketch.* (1) [Leibniz rule](../../l-theory/localization/products/product-leibniz.md) and [products commute with T](../../l-theory/localization/products/product-involution.md), with [circle duality](circle-duality.md) (2) and $T\varphi_P=\varphi_P$. (2) By the [duality map of a product](../../l-theory/localization/products/product-duality-map.md), $(\varphi_i)_\natural=(\varphi^s\otimes\dots\otimes\varphi^s\otimes\varphi_P)\circ\Xi$, and likewise for $\varphi_i^u$. So $(\varphi^u_i)_\natural b_i=(\varphi b)^{\otimes n}\otimes\varphi_Pb_P=1$, $b_i(\varphi_i^u)_\natural=\Xi^{-1}\Xi=1$, $\varphi_ib_i=A^{\otimes n}\otimes1$ and $b_i\varphi_i=\Xi^{-1}(A'^{\otimes n}\otimes1)\Xi$. Telescope $A^{\otimes n}-1=\sum_j1^{\otimes(j-1)}\otimes(A-1)\otimes A^{\otimes(n-j)}$ and use $A-1=dK+Kd$ from circle duality (3); with the sign rule, $d(1\otimes K\otimes A)+(1\otimes K\otimes A)d=1\otimes(dK+Kd)\otimes A$. The same for $A'$, and $\Xi$ is an isomorphism of complexes. (3) Each tensor factor moves only its own coordinate, by at most $h_i/2$ for $\varphi^s,b,K,K'$ and at most $h_i$ for $A,A'$ (circle duality (5)), and $\Xi$ has propagation $0$. (4) A block landing in degree $0$ has every $p_j=0$, so its sign is $+1$. For a top cube $c$, $\varphi_i((c\otimes e_4)^*)$ has degree-$0$ part $\bigotimes_j\varphi^s(e_{w_j}^*)\otimes e_0$, whose augmentation is $1$ by circle duality (4) and $\varepsilon e_0=1$. And $z_i$ is the sum of the top cells $c\otimes e_4$, each with coefficient $1$.

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: replaces the cap-block comparison of HS paper, Section 7.
## Depends on
- [The cells of CP^2 vanish in negative degrees](cp2-dim-neg.md)
- [circle structure](circle-data/circle-phi.md), [symmetric circle structure](circle-data/circle-phi-sym.md), [circle inverse](circle-data/circle-b.md), [circle homotopy](circle-data/circle-k.md), [dual circle homotopy](circle-data/circle-k-dual.md)
- [Chain-model duality](chain-model-duality.md), [chain model](chain-model.md), [propagation](../../categories/asymptotic/propagation.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md), [tensor product of based complexes](based-complex-tensor.md), [tensor of graded maps](tensor/based-tensor-hom.md), [dual tensor of graded maps](tensor/based-dual-tensor-hom.md), [identity of degree zero](tensor/id-deg0.md), [circle duality](circle-duality.md), [cells of CP^2](cp2-cells.md), [the involution T](../../l-theory/base/complexes/structure-involution.md)
## Proof depends on
- [Circle duality](circle-duality.md), [cells of CP^2](cp2-cells.md), [Leibniz rule for products](../../l-theory/localization/products/product-leibniz.md), [products commute with T](../../l-theory/localization/products/product-involution.md), [duality map of a product](../../l-theory/localization/products/product-duality-map.md)
