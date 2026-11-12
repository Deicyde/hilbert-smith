---
article_id: af_95cabb7413e73b69a3c1ac7c
declaration: abbrev
origin: bridged
statement: formalized
lean: HSP.AsymCat
---

# Asymptotic category

Let $X$ be a compact metric space with an isometric $C_p$-action and let $\mathbf G$ be a [group sequence](group-sequence.md). An object of $\mathcal A_{\mathbf G}(X)$ is a sequence $(n_i,x_i)$ with $n_i\in\mathbb N$ and $x_i:\{1..n_i\}\to X$. Its basis at $i$ is the free $G_i$-set $B_i=G_i\times\{1..n_i\}$, with labels $\lambda_i(g,k)=\chi_i(g)x_i(k)$. A morphism is a sequence of $G_i$-equivariant matrices $u_i\in\mathbb Q^{B'_i\times B_i}$ with $\operatorname{prop}(u_i)\to0$, taken modulo eventual equality. Each $u_i$ is a morphism of [$\mathrm{Free}(\mathbb Q[G_i])$](free-category.md), the $i$-th coordinate of $u$; a sequence is determined by its coordinates, and $[u]$ denotes its class. Composition and addition are levelwise, so the category is preadditive and $\mathbb Q$-linear. Its biproducts, given by concatenating the $x_i$, are constructed separately in the section on its structure.

The construction needs neither compactness of $X$ nor that the action is isometric.

## Sources

- HS paper, Section 2

## Depends on

- [Propagation](propagation.md)
- [Group sequence](group-sequence.md)
- [Free category of a finite group](free-category.md)

## Proof depends on

- [Propagation of the identity](prop-one.md)
- [Propagation of a sum](prop-add.md)
- [Propagation of a scalar multiple](prop-smul.md)
- [Propagation of a product](prop-mul.md)
- [The trivial group sequence](trivial-group-sequence.md)
