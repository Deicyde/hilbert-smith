---
article_id: af_c67dd22aa84af5711464be4b
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.chainModelDuality
---
# Chain-model duality

The duality data of $D_i$ are a structure $\varphi_i\in M(D_i)_N$ and a map $b_i:D_i\to D_i^{N-*}$, built from $\varphi^s,b$ of [circle duality](circle-duality.md) on $S=S_{k_i}$ and the [structure](cp2/cp2-structure.md) $\varphi_P$ and its [inverse](cp2/cp2-inverse.md) $b_P$ on the [cellular chain complex $P$ of CP^2](cp2/cp2-complex.md). All products are computed in the explicit bases of the [tensor product of based complexes](based-complex-tensor.md), and the iterations start, like $C(k_i)$, from the unit complex $\mathbb 1$ with [structure](model/unit-structure.md) and map the identity of $\mathbb Q$ in degree $0$; the first step multiplies by the unit with sign $+1$.

1. $\varphi_i=(\cdots(\varphi^s\otimes\varphi^s)\otimes\cdots\otimes\varphi^s)\otimes\varphi_P$, the [structure of the grid complex](model/grid-structure.md) times $\varphi_P$, is the iterated [product of structures in explicit bases](tensor/structure-products/based-str-prod.md), the based form of the external product of structures on the tensor product of based complexes: the product of $\phi\in M(A)_m$ and $\theta\in M(B)_{m'}$ has the block $(-1)^{q(p+m)}\phi_p\otimes\theta_q$ from $A^*_{m-p}\otimes B^*_{m'-q}$ to $A_p\otimes B_q$, where the dual of a basis element $x\otimes y$ is identified with $x^*\otimes y^*$, with no sign. Explicitly (not formalized), for a basis cell $x_1\otimes\dots\otimes x_n\otimes e$,
$$\varphi_i\bigl((x_1\otimes\dots\otimes x_n\otimes e)^*\bigr)=(-1)^{\sum_jp_j(p_1+\dots+p_{j-1}+j-1)}\,\varphi^s(x_1^*)\otimes\dots\otimes\varphi^s(x_n^*)\otimes\varphi_P(e^*),$$
where $p_j=1-\dim x_j$ is the degree of $\varphi^s(x_j^*)$. The factor $\varphi_P$ adds no sign, because $P$ is concentrated in even degrees.
2. $b_i=\Xi^{-1}\circ(b\otimes\dots\otimes b\otimes b_P)$, given by its components $(b_i)_r:(D_i)_r\to(D_i^{N-*})_r$; on the summand $A_a\otimes B_c$ it is $(-1)^{c(a+m)}f_a\otimes g_c$ into the dual of $A_{m-a}\otimes B_{m'-c}$, for the factors $f$ of $A$ and $g$ of $B$ at each step. Here $b\otimes\dots\otimes b_P:D_i\to S^{1-*}\otimes\dots\otimes S^{1-*}\otimes P^{4-*}$ is the tensor of chain maps of degree $0$, which has no signs, and $\Xi:D_i^{N-*}\to S^{1-*}\otimes\dots\otimes S^{1-*}\otimes P^{4-*}$ is the iterated isomorphism of the dual of a tensor product, with sign $(-1)^{b(a+m)}$ on the summand $(A_{m-a}\otimes B_{m'-b})^*$ at each step.

**Remark (not formalized).** For $n=2$ and the top cell $e_v\otimes e_w\otimes e_4$, every block landing in degree $0$ has $p_1=p_2=0$, so its sign is $+1$: $\varphi_i((e_v\otimes e_w\otimes e_4)^*)$ has degree-$0$ part $\tfrac14([v]+[v+1])\otimes([w]+[w+1])\otimes e_0$. For the edge $[v]\otimes e_w\otimes e_4$ ($p_1=1$, $p_2=0$), the sign is $(-1)^{0\cdot(1+1)}=+1$; for $e_v\otimes[w]\otimes e_4$ ($p_1=0$, $p_2=1$) it is $(-1)^{1\cdot(0+1)}=-1$.

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: the cubical tensor form.
## Depends on
- [The iterated grid duality map](poincare/grid-factor/grid-dual-map.md)
- [The structure of the grid complex](model/grid-structure.md)
- [The cellular chain complex of CP^2](cp2/cp2-complex.md)
- [The structure of CP^2](cp2/cp2-structure.md)
- [The inverse of the structure of CP^2](cp2/cp2-inverse.md)
- [The circle complex](cubical/circle-complex.md)
- [The circle complex vanishes in negative degrees](cubical/circle-dim-neg.md)
- [The unit complex](cubical/unit-complex.md)
- [The structure of the unit complex](model/unit-structure.md)
- [Cubical torus grid](cubical/cubical-torus-grid.md)
- [Product of structures in explicit bases](tensor/structure-products/based-str-prod.md), [product of duality maps in explicit bases](tensor/structure-products/based-dual-prod.md)
- [The cells of CP^2 vanish in negative degrees](cp2/cp2-dim-neg.md)
- [symmetric circle structure](poincare/circle-data/circle-phi-sym.md), [circle inverse](poincare/circle-data/circle-b.md)
- [Chain model](model/chain-model.md), [circle duality](circle-duality.md), [tensor product of based complexes](based-complex-tensor.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md), [structure complex](../../l-theory/base/complexes/structure-complex.md), [dual complex](../../l-theory/base/complexes/dual-complex.md)
