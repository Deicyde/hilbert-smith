---
article_id: af_e1f03805ebacf59bc9085346
declaration: instance
origin: background
statement: formalized
lean: HSP.FreeQ.instDualCat
---

# Based vector spaces

$\mathbb Q$ also denotes the duality category whose objects are the based vector spaces $\mathbb Q^d$ ($d\ge0$), whose morphisms $\mathbb Q^d\to\mathbb Q^{d'}$ are the $d'\times d$ rational matrices, with composition the matrix product, sums and rational multiples of matrices taken entrywise, finite biproducts (the block inclusions and projections make $\mathbb Q^{d+d'}$ a biproduct of $\mathbb Q^d$ and $\mathbb Q^{d'}$, and $\mathbb Q^0$ is a zero object), and the duality $(\mathbb Q^d)^*=\mathbb Q^d$, $g^*=g^{\mathsf T}$ (transpose). Both identities $M^{**}=M$ and $g^{**}=g$ hold on the nose. The standard basis vector $e_i$ of $\mathbb Q^d$ has dual basis vector $e_i^*$, the same vector of $(\mathbb Q^d)^*$.

## Sources

- [Ranicki 1992, §1, free modules with the transpose duality](../../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Duality category](../../base/categories/duality-category.md)
