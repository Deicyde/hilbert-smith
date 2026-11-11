---
article_id: af_1fb521100ae4c7e68ac12183
declaration: instance
origin: bridged
statement: formalized
lean: HSP.FreeCat.dualCat
---

# Free category of a finite group

Let $G$ be a finite group, written additively. The duality category $\mathrm{Free}(\mathbb Q[G])$ is defined as follows.

- An object is a number $n\in\mathbb N$. Its basis is the free $G$-set $G\times\{1..n\}$, with $G$ acting on the first factor.
- A morphism $n\to m$ is a $G$-equivariant rational matrix $u\in\mathbb Q^{(G\times\{1..m\})\times(G\times\{1..n\})}$, that is, $u_{(g+h,k'),(g+h',k)}=u_{(h,k'),(h',k)}$ for all $g$. Composition is the matrix product and the identity is the identity matrix.
- The sum of $n$ and $m$ is $n+m$, with the coordinate inclusions and projections; the zero object is $0$.
- The duality is strict: $n^*=n$ and $u^*=u^{T}$.

For $G=1$ this is $\mathrm{Free}(\mathbb Q)$, whose morphisms $n\to m$ are the rational $m\times n$ matrices.

*Proof sketch.* Products and transposes of equivariant matrices are equivariant. Transposition is $\mathbb Q$-linear, reverses products and is an involution on the nose.

## Sources

- HS paper, Section 3
- [Ranicki 1992, §1, based free modules](../../../../sources/paper/ranicki-1992.md) [U]

## Depends on

- [Small Q-linear category with strict duality](../../l-theory/base/categories/duality-category.md)
