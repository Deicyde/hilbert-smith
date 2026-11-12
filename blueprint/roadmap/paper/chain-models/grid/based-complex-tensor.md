---
article_id: af_07ab67f0b8c5d3a2ab8bfe5a
declaration: def
origin: background
statement: formalized
lean: HSP.ChainModels.basedComplexTensor
---

# Tensor product of based complexes

Let $C$ and $D$ be chain complexes in the duality category $\mathbb Q$ of [based vector spaces](../../l-theory/localization/products/based-vector-spaces.md), with $C_p=\mathbb Q^{c_p}$, $D_q=\mathbb Q^{d_q}$, and $D_q=0$ for $q<0$. Their tensor product $C\otimes D$ is the complex with
$$(C\otimes D)_r=\mathbb Q^{N_r},\qquad N_r=\sum_{p=0}^{r}c_pd_{r-p},$$
for $r\ge0$, and $(C\otimes D)_r=0$ for $r<0$. Its basis is the concatenation of the bases of the summands $C_p\boxtimes D_{r-p}$, $0\le p\le r$, in increasing order of $p$, and inside a summand $x_i\otimes y_j$ is the basis vector $e_{(i-1)d_{r-p}+j}$, as in the [tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md). On the summand $C_p\boxtimes D_q$ the differential is
$$d\boxtimes1+(-1)^p\,1\boxtimes d:\ C_p\boxtimes D_q\to(C_{p-1}\boxtimes D_q)\oplus(C_p\boxtimes D_{q-1}),$$
where $\boxtimes$ of matrices is the Kronecker product. The components are the dimensions $c_pd_{r-p}$ of the summands, the [block inclusions and projections](tensor/blocks/block-maps.md) $\iota_p:\mathbb Q^{c_pd_{r-p}}\to\mathbb Q^{N_r}$ and $\pi_p:\mathbb Q^{N_r}\to\mathbb Q^{c_pd_{r-p}}$ of the concatenation, and the differential, assembled from its blocks between summands. When $C_p=0$ for $p<0$ as well, the summands $C_p\boxtimes D_{r-p}$, $0\le p\le r$, are all the $C_p\boxtimes D_q$ with $p+q=r$.

*Proof sketch.* ($d^2=0$.) Write the differential blockwise, with the block inclusions and projections of the concatenation, which satisfy $\pi_{p'}\iota_p=\delta_{pp'}$. The block of $d^2$ from $C_p\boxtimes D_q$ to $C_{p''}\boxtimes D_{q''}$ is $d^2\boxtimes1=0$ if $p''=p-2$, $1\boxtimes d^2=0$ if $p''=p$, and $(-1)^{p-1}d\boxtimes d+(-1)^pd\boxtimes d=0$ if $p''=p-1$, by the mixed-product rule for Kronecker products. In the last case both intermediate summands exist unless the target summand $C_{p-1}\boxtimes D_{q-1}$ has $q-1<0$, and then it is zero.

**Remark (not formalized).** Up to the canonical isomorphism of the concatenated sums with the direct sums, this is the [tensor product of complexes](../../l-theory/localization/products/complex-product.md) for the pairing of the tensor product of based vector spaces; here the bases are explicit, so that cells are basis vectors and propagation is read off matrix entries.

## Sources

- New: explicit bases for the chain models.

## Depends on

- [Based vector spaces](../../l-theory/localization/products/based-vector-spaces.md)
- [Tensor product of based vector spaces](../../l-theory/localization/products/based-tensor.md)
- [Block inclusions and projections](tensor/blocks/block-maps.md)
