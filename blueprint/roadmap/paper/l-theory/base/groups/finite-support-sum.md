---
article_id: af_f32b446b006211a14f424808
declaration: lemma
origin: bridged
---

# Finite-support sum

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](../../../categories/asymptotic/group-sequence.md), let $\mathcal S_{\mathbf G}\subset\mathcal P_{\mathbf G}=\prod_i\mathrm{Free}(G_i)$ be the [finite-support subcategory](../../../categories/asymptotic/eventually-zero-subcategory.md) of the [sequence category](../../../categories/asymptotic/point-sequence-category.md), and let $\pi_i:\mathcal S_{\mathbf G}\to\mathrm{Free}(G_i)$ be the coordinate functors, with $\mathrm{Free}(G_i)$ the [free category](../../../categories/asymptotic/free-category.md). Then $(\pi_{i*})_i:L^p_k(\mathcal S_{\mathbf G})\to\bigoplus_iL^p_k(\mathrm{Free}(G_i))$ is an isomorphism.

*Proof sketch.* (1) For finite $F\subset\mathbb N$ let $\mathcal S_F\subset\mathcal S_{\mathbf G}$ be the full subcategory of sequences $(n_i)$ with $n_i=0$ for $i\notin F$. Restriction $\mathcal S_F\to\prod_{i\in F}\mathrm{Free}(G_i)$ is a strict duality functor. Extension by the object $0$ is a strict duality functor in the other direction, and both composites are the identity functors. So $L^p_k(\mathcal S_F)\cong L^p_k(\prod_{i\in F}\mathrm{Free}(G_i))$ by [Functoriality on L^p](lp-functoriality.md). (2) Every object of $\mathcal S_{\mathbf G}$ lies in some $\mathcal S_F$. A complex in $\mathrm{Kar}\,\mathcal S_{\mathbf G}$, after its chain objects outside $[0,k]$ are replaced by a zero object (a structure-preserving isomorphism), has finitely many chain objects, so it lies in $\mathrm{Kar}\,\mathcal S_F$ for some $F$; the same holds for a cobordism. With [Homotopy-isometry invariance](homotopy-isometry-invariance.md) and [Transport of pairs along isomorphisms](../pairs/pair-transport.md) for the replacements, $L^p_k(\mathcal S_{\mathbf G})=\mathrm{colim}_FL^p_k(\mathcal S_F)$ along the strict inclusions. (3) [Products](product.md) for each $F$, by induction on the size of $F$. (4) A directed colimit of finite sums is the direct sum, compatibly with the coordinate functors.

## Sources

- HS paper, Section 3 (statement only)
- New: finite-block argument at the level of strict complexes

## Depends on

- [Induced homomorphism](induced-map.md)
- [Group sequence](../../../categories/asymptotic/group-sequence.md)
- [Free category](../../../categories/asymptotic/free-category.md)
- [Sequence category](../../../categories/asymptotic/point-sequence-category.md)
- [Finite-support subcategory](../../../categories/asymptotic/eventually-zero-subcategory.md)

## Proof depends on

- [Functoriality on L^p](lp-functoriality.md)
- [Homotopy-isometry invariance](homotopy-isometry-invariance.md)
- [Transport of pairs along isomorphisms](../pairs/pair-transport.md)
- [Products](product.md)
