---
article_id: af_f32b446b006211a14f424808
declaration: lemma
origin: bridged
---

# Finite-support sum

Let $G_i$ ($i\in\mathbb N$) be finite groups, and let $\mathrm{Free}(\mathbb Q[G_i])$ have the duality transpose-with-$g\mapsto g^{-1}$. Let $\mathcal S\subset\prod_i\mathrm{Free}(\mathbb Q[G_i])$ be the full subcategory of sequences $(M_i)$ such that $M_i$ is a zero object for all but finitely many $i$. Then the coordinate functors induce an isomorphism $L^p_k(\mathcal S)\to\bigoplus_iL^p_k(\mathrm{Free}(\mathbb Q[G_i]))$.

*Proof sketch.* (1) For finite $F\subset\mathbb N$ let $\mathcal S_F\subset\mathcal S$ be the full subcategory of sequences with $M_i$ a zero object for $i\notin F$. Restriction $\mathcal S_F\to\prod_{i\in F}\mathrm{Free}(\mathbb Q[G_i])$ is a strict duality functor. Extension by chosen zero objects is a duality functor whose $\xi$ is the identity in the slots of $F$ and the unique isomorphism between zero objects elsewhere. The two composites are unitarily isomorphic to the identities by the same recipe, so [Equivalence invariance](equivalence-invariance.md) identifies $L^p_k(\mathcal S_F)$ with $L^p_k(\prod_{i\in F}\mathrm{Free}(\mathbb Q[G_i]))$. (2) Every object of $\mathcal S$ lies in some $\mathcal S_F$. A complex in $\mathrm{Kar}\,\mathcal S$, after its chain objects outside $[0,k]$ are replaced by a zero object (a structure-preserving isomorphism), has finitely many chain objects, so it lies in $\mathrm{Kar}\,\mathcal S_F$ for some $F$; the same holds for a cobordism. With [Homotopy-isometry invariance](homotopy-isometry-invariance.md) and [Transport of pairs along isomorphisms](../pairs/pair-transport.md) for the replacements, $L^p_k(\mathcal S)=\mathrm{colim}_FL^p_k(\mathcal S_F)$ along the strict inclusions. (3) [Products](product.md) for each $F$. (4) A directed colimit of finite sums is the direct sum, compatibly with the coordinate functors.

## Sources

- HS paper, Section 3 (statement only)
- New: finite-block argument at the level of strict complexes

## Depends on

- [Induced homomorphism](induced-map.md)

## Proof depends on

- [Equivalence invariance](equivalence-invariance.md)
- [Homotopy-isometry invariance](homotopy-isometry-invariance.md)
- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Products](product.md)
