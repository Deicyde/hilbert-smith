---
article_id: af_c67dd22aa84af5711464be4b
declaration: def
origin: bridged
---
# Chain-model duality

The duality data of $D_i$ are a structure $\varphi_i\in M(D_i)_N$ and a map $b_i:D_i\to D_i^{N-*}$, built from $\varphi^s,b$ of [circle duality](circle-duality.md) on $S=S_{k_i}$ and $\varphi_P,b_P$ of the [cells of CP^2](cp2-cells.md).

1. $\varphi_i=(\cdots(\varphi^s\otimes\varphi^s)\otimes\cdots\otimes\varphi^s)\otimes\varphi_P$ is the iterated [external product of structures](../../l-theory/localization/products/external-product.md): the product of $\phi\in M(A)_m$ and $\theta\in M(B)_{m'}$ has the block $(-1)^{q(p+m)}\phi_p\otimes\theta_q$ from $A^*_{m-p}\otimes B^*_{m'-q}$ to $A_p\otimes B_q$, where the dual of a basis element $x\otimes y$ is identified with $x^*\otimes y^*$, with no sign. Explicitly, for a basis cell $x_1\otimes\dots\otimes x_n\otimes e$,
$$\varphi_i\bigl((x_1\otimes\dots\otimes x_n\otimes e)^*\bigr)=(-1)^{\sum_jp_j(p_1+\dots+p_{j-1}+j-1)}\,\varphi^s(x_1^*)\otimes\dots\otimes\varphi^s(x_n^*)\otimes\varphi_P(e^*),$$
where $p_j=1-\dim x_j$ is the degree of $\varphi^s(x_j^*)$. The factor $\varphi_P$ adds no sign, because $P$ is concentrated in even degrees.
2. $b_i=\Xi^{-1}\circ(b\otimes\dots\otimes b\otimes b_P)$. Here $b\otimes\dots\otimes b_P:D_i\to S^{1-*}\otimes\dots\otimes S^{1-*}\otimes P^{4-*}$ is the tensor of chain maps of degree $0$, which has no signs, and $\Xi:D_i^{N-*}\to S^{1-*}\otimes\dots\otimes S^{1-*}\otimes P^{4-*}$ is the iterated isomorphism of the [dual of a tensor product](../../l-theory/localization/products/product-dual-iso.md), with sign $(-1)^{b(a+m)}$ on the summand $(A_{m-a}\otimes B_{m'-b})^*$ at each step.

**Remark (not formalized).** For $n=2$ and the top cell $e_v\otimes e_w\otimes e_4$, every block landing in degree $0$ has $p_1=p_2=0$, so its sign is $+1$: $\varphi_i((e_v\otimes e_w\otimes e_4)^*)$ has degree-$0$ part $\tfrac14([v]+[v+1])\otimes([w]+[w+1])\otimes e_0$. For the edge $[v]\otimes e_w\otimes e_4$ ($p_1=1$, $p_2=0$), the sign is $(-1)^{0\cdot(1+1)}=+1$; for $e_v\otimes[w]\otimes e_4$ ($p_1=0$, $p_2=1$) it is $(-1)^{1\cdot(0+1)}=-1$.

## Sources
- [Ranicki 1980, products](../../../../sources/paper/ranicki-1980.md) [U]. New: the cubical tensor form.
## Depends on
- [Chain model](chain-model.md), [circle duality](circle-duality.md), [cells of CP^2](cp2-cells.md), [external product of structures](../../l-theory/localization/products/external-product.md), [dual of a tensor product](../../l-theory/localization/products/product-dual-iso.md), [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md)
