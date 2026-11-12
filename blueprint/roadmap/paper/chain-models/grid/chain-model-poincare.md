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
satisfy $\varphi_ib_i-1=dH_i+H_id$ and $b_i\varphi_i-1=dH'_i+H'_id$. Tensors of maps carry the sign $(f\otimes g)(x\otimes y)=(-1)^{|g||x|}f(x)\otimes g(y)$, and are computed in the explicit bases of the tensor product of based complexes; the sums are formed by the telescoping recursion $H^{(j+1)}=H^{(j)}\otimes A+1\otimes K$ from $H^{(0)}=0$ on the unit complex, $H_i=H^{(n)}\otimes1_P$, and likewise for $H'_i$ through $\Xi$;
3. with cells labelled at their centers, $\varphi_i,b_i,H_i,H'_i$ have $d_\infty$-propagation at most $h_i$;
4. $\varepsilon\varphi_i(\alpha)=\alpha(z_i)$ for every $\alpha\in D_N^*$, the degree-$0$ part of $D_i^{N-*}$, where $\varepsilon=\varepsilon^{\otimes n}\otimes\varepsilon_P$ on $(D_i)_0=C(k_i)_0\otimes P_0$.

*Proof sketch.* The theorem is the conjunction of its four parts, each a separate lemma: [the cycle](poincare/chain-model-poincare-cycle.md) (1), [the inverse and the homotopies](poincare/chain-model-poincare-inverse.md) (2), [propagation](poincare/chain-model-poincare-propagation.md) (3) and [the augmentation](poincare/chain-model-poincare-augmentation.md) (4).

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: replaces the cap-block comparison of HS paper, Section 7.
## Depends on

- [Torus labels of chain-model cells](model/chain-model-label.md)
- [Fundamental cycle of the chain model](model/chain-model-fundamental.md)
- [The unsymmetrized structure of the chain model](poincare/chain-model-structure-u.md)
- [The homotopy of the chain model](poincare/chain-model-h.md)
- [The dual homotopy of the chain model](poincare/chain-model-h-dual.md)
- [The augmentation of the chain model](poincare/chain-model-aug.md)
- [Chain-model duality](chain-model-duality.md)
- [Chain model](model/chain-model.md)
- [Propagation](../../categories/asymptotic/propagation.md)
- [The involution T](../../l-theory/base/complexes/structure-involution.md)
- [Mesh sequence](mesh-sequence.md)
- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
- [Dual complex](../../l-theory/base/complexes/dual-complex.md)
- [Structure complex](../../l-theory/base/complexes/structure-complex.md)
- [Local datum](../../local-data/chart/local-datum.md)

## Proof depends on

- [The chain model is Poincaré: the cycle](poincare/chain-model-poincare-cycle.md)
- [The chain model is Poincaré: the inverse and the homotopies](poincare/chain-model-poincare-inverse.md)
- [The chain model is Poincaré: propagation](poincare/chain-model-poincare-propagation.md)
- [The chain model is Poincaré: the augmentation](poincare/chain-model-poincare-augmentation.md)
