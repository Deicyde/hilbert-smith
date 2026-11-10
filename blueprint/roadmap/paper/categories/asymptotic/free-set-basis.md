---
article_id: af_2253db73e9a5eee745e7923f
declaration: lemma
origin: bridged
---

# Bases of finite free G-sets

Let $G$ be a finite group and $B,B'$ finite free $G$-sets with enumerated orbit representatives $b_1,\dots,b_n\in B$ and $b'_1,\dots,b'_m\in B'$. Put $\varphi(g,k)=g\,b_k$ and $\varphi'(g,k)=g\,b'_k$. Then $\varphi:G\times\{1..n\}\to B$ and $\varphi'$ are equivariant bijections, and reindexing, $u\mapsto(u_{\varphi'(c'),\varphi(c)})_{c',c}$, is a bijection from the $G$-equivariant matrices in $\mathbb Q^{B'\times B}$ onto the morphisms $n\to m$ of [$\mathrm{Free}(\mathbb Q[G])$](free-category.md). Reindexing is $\mathbb Q$-linear and preserves identity matrices, products and transposes.

*Proof sketch.* $\varphi$ is onto because every orbit contains some $b_k$, and injective because the action is free and the $b_k$ lie in distinct orbits. It commutes with the action, so reindexing carries equivariant matrices to equivariant matrices; reindexing along $\varphi^{-1}$ inverts it. Reindexing along a bijection commutes with sums, products and transposition.

## Sources

- New: identifies the model of [$\mathrm{Free}(\mathbb Q[G])$](free-category.md) on the standard bases $G\times\{1..n\}$ with matrices on arbitrary finite free $G$-sets, as used for restriction to a subgroup and for tensoring with a permutation module.

## Depends on

- [Free category of a finite group](free-category.md)
