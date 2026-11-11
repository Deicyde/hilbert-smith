---
article_id: af_d954bb703e948a36e303def2
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
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

*Proof sketch.* The four parts are separate lemmas: [the cycle](poincare/chain-model-poincare-cycle.md), [the inverse and the homotopies](poincare/chain-model-poincare-inverse.md), [propagation](poincare/chain-model-poincare-propagation.md) and [the augmentation](poincare/chain-model-poincare-augmentation.md). (1) [Leibniz rule](tensor/structure-products/str-prod-leibniz.md) and [products commute with T](tensor/structure-products/str-prod-involution.md), with [circle duality](circle-duality.md) (2) and $T\varphi_P=\varphi_P$. (2) In explicit bases, a [product of duality maps composed with a product of structures](tensor/structure-products/dual-prod-comp-str-prod.md) is the tensor of the factorwise composites, and a [product of structures composed with a product of duality maps](tensor/structure-products/str-prod-comp-dual-prod.md) is the dual tensor $\Xi^{-1}(\cdots)\Xi$ of the factorwise composites; this applies to $\varphi_i$ and to $\varphi_i^u$. So $(\varphi^u_i)_\natural b_i=(\varphi b)^{\otimes n}\otimes\varphi_Pb_P=1$, $b_i(\varphi_i^u)_\natural=\Xi^{-1}\Xi=1$, $\varphi_ib_i=A^{\otimes n}\otimes1$ and $b_i\varphi_i=\Xi^{-1}(A'^{\otimes n}\otimes1)\Xi$. Telescope $A^{\otimes n}-1=\sum_j1^{\otimes(j-1)}\otimes(A-1)\otimes A^{\otimes(n-j)}$ and use $A-1=dK+Kd$ from circle duality (3); with the sign rule, $d(1\otimes K\otimes A)+(1\otimes K\otimes A)d=1\otimes(dK+Kd)\otimes A$. The same for $A'$, and $\Xi$ is an isomorphism of complexes. (3) Each tensor factor moves only its own coordinate, by at most $h_i/2$ for $\varphi^s,b,K,K'$ and at most $h_i$ for $A,A'$ (circle duality (5)), and $\Xi$ has propagation $0$. (4) For a top cube $c$, $\varphi_i((c\otimes e_4)^*)$ has degree-$0$ part $\bigotimes_j\varphi^s(e_{w_j}^*)\otimes e_0$, whose augmentation is $1$ by circle duality (4) and $\varepsilon e_0=1$. And $z_i$ is the sum of the top cells $c\otimes e_4$, each with coefficient $1$.

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: replaces the cap-block comparison of HS paper, Section 7.
## Depends on
- [Torus labels of chain-model cells](model/chain-model-label.md)
- [Fundamental cycle of the chain model](model/chain-model-fundamental.md)
- [The cells of CP^2 vanish in negative degrees](cp2/cp2-dim-neg.md)
- [The unsymmetrized structure of the chain model](poincare/chain-model-structure-u.md), [the homotopy of the chain model](poincare/chain-model-h.md), [the dual homotopy of the chain model](poincare/chain-model-h-dual.md), [the augmentation of the chain model](poincare/chain-model-aug.md)
- [circle structure](poincare/circle-data/circle-phi.md), [symmetric circle structure](poincare/circle-data/circle-phi-sym.md), [circle inverse](poincare/circle-data/circle-b.md), [circle homotopy](poincare/circle-data/circle-k.md), [dual circle homotopy](poincare/circle-data/circle-k-dual.md)
- [Product of structures in explicit bases](tensor/structure-products/based-str-prod.md), [product of duality maps in explicit bases](tensor/structure-products/based-dual-prod.md)
- [Chain-model duality](chain-model-duality.md), [chain model](model/chain-model.md), [propagation](../../categories/asymptotic/propagation.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md), [tensor product of based complexes](based-complex-tensor.md), [tensor of graded maps](tensor/based-tensor-hom.md), [dual tensor of graded maps](tensor/based-dual-tensor-hom.md), [identity of degree zero](tensor/id-deg0.md), [circle duality](circle-duality.md), [cells of CP^2](cp2/cp2-cells.md), [the involution T](../../l-theory/base/complexes/structure-involution.md)
## Proof depends on
- [The chain model is Poincaré: the cycle](poincare/chain-model-poincare-cycle.md), [the inverse and the homotopies](poincare/chain-model-poincare-inverse.md), [propagation](poincare/chain-model-poincare-propagation.md), [the augmentation](poincare/chain-model-poincare-augmentation.md)
