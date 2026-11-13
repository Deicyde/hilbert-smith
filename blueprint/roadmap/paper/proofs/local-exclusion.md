---
article_id: af_251cccb60e3303ff0ab37e1a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: HSP.localExclusion
---

# Local exclusion

Let $p$ be a prime, $n\in\mathbb N$, and $O\subseteq\mathbb{R}^n$ a nonempty connected open set. No jointly continuous action of $\mathbb{Z}_p$ on $O$ is faithful.

*Proof sketch.*
1. If $n=0$, $O$ is a point, and $0$ and $1$ act alike.
2. Otherwise suppose the action is faithful. $O$ is a connected $n$-manifold, so it carries fixed local data with $D=1/64$, with buffer radius $R$, control space $T$ (possibly empty) and torus test map $f_T$. Fix $s=R/(2\sqrt n)$, so $0<s<R/\sqrt n$, and let $G_i=\mathbb Z/p^{\max(i,1)}$ for $i\in\mathbb N$, with $\chi_i$ reduction modulo $p$, so that every $\chi_i$ is onto (level $0$ carries nothing, since the compressed complex vanishes below its start index $i_0\ge1$). Let $Z_0$ be the exterior for $n$ and $R$, $Z=T\times Z_0$, and let $\Delta_{\mathbf 1}$ be the scalar iterated cut for this $n$, $R$ and $s$; it needs no control space, and both Theorem B (step 3) and Theorem A (step 6) are applied to this $\Delta_{\mathbf 1}$.
3. The torus test map is continuous, as the start of a continuous homotopy to the cubical pinch ([the torus test map is homotopic to the cubical pinch](../evaluation/test-map-to-pinch.md)). Theorem B for the test map, with this $s$, gives $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})=[(\varepsilon,\varepsilon,\dots)]$ with $\varepsilon\in\{\pm1\}$, for the labelled-model class $\mathfrak m_{f_T}$.
4. Theorem C gives the compressed complex $(C,\hat\varphi)$, a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$ concentrated in $[0,N]$ (clause 1), with $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}$ (clause 3), where $U'$ is forgetting to the scalar exterior quotient for $T$, $R$ and the trivial group sequence, and $\operatorname{cls}(C,\hat\varphi)$ is $\operatorname{cls}$ of the image of $(C,\hat\varphi)$ under the Karoubi embedding $M\mapsto(M,1)$.
5. Case $T=\varnothing$. Then $\operatorname{cls}(C,\hat\varphi)=0$ by [the class over an empty space vanishes](empty-control-class.md), since $T\times S^n$ is empty. By step 4, $\mathfrak m_{f_T}=U'_*0=0$. As $\Delta_{\mathbf 1}$ (a composite of induced maps, cut boundaries and inverses of induced isomorphisms) and $\sigma_{\mathrm{tail}}$ are homomorphisms, step 3 gives $[(\varepsilon,\varepsilon,\dots)]=0$, so $\varepsilon=0$ for all large $i$, which is false.
6. Case $T\ne\varnothing$. By Theorem C (clause 2), $p$, $(G_i,\chi_i)$, $T$, $n$, $R$ and $s$ form standing data (the [standing data of the compression](../compression/compressed-standing-data.md)), and $(C,\hat\varphi)$ carries a graph-type homotopy action of $\mathbf G=(G_i,\chi_i)$. Theorem A, applied to $(C,\hat\varphi)$, says that every representative of $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}U'_*\operatorname{cls}(C,\hat\varphi))=\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})$ is eventually divisible by $p$. By step 3, $(\varepsilon,\varepsilon,\dots)$ is such a representative. The lemma on integer tails, for the constant sequence $\varepsilon$, gives a contradiction.

This proof rests on the open statements Newman's theorem on fixing an open set (through the fixed local data), lifting (through every cut boundary and the tail signature), the two sides of an excision boundary (through the inner cuts of Theorem B), Lemma U (through the tail signature) and idempotent splitting in the bounded homotopy category (through Theorem A). Until their proofs are formalized, it also rests on these stated results: Theorem A; Theorem C, with Chain-model estimates, Chain approximations exist, Isometry homotopies and Product homotopies (through the compressed complex); Homotopic labellings have equal classes, Evaluation at the cubical pinch, The labelled chain model is Poincaré and Constant tail (through Theorem B); Transition commutes with the boundary, Products with the line are decorated, Lifting closed complexes and Independence of the lift (through every cut boundary and the ultimate boundary); Point comparison for the free categories, Boundaries have zero signature, The middle form is nonsingular, symmetric and invariant, Middle form of a sum, Classes over $\mathcal V$ lift and Lifts agree eventually (through the tail signature); Naturality of the transition (through the induced maps on ultimate L-groups); and Cobordism is an equivalence relation (through every L-group).

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (Proposition 13.1 and the proof of Theorem 1.1)
- [HS paper, Section 4](../../../sources/hs-paper.md#section-4-divisibility-over-a-free-c_p-space-algobstruction-lines-317-380)
- New: the contradiction is assembled from Theorems A, B and C as stated in this paper, with $T$ the control space of the fixed local data

## Depends on

## Proof depends on

- [Fixed local data from a faithful action](../local-data/control/fixed-local-data-exists.md)
- [Standing data of the compression](../compression/compressed-standing-data.md)
- [Theorem B for the test map](../evaluation/theorem-b-test-map.md)
- [The torus test map is homotopic to the cubical pinch](../evaluation/test-map-to-pinch.md)
- [Theorem C](../compression/theorem-c.md)
- [Theorem A](../corner/theorem/theorem-a.md)
- [Integer tails](integer-tails.md)
- [The class over an empty space vanishes](empty-control-class.md)
- [Torus test map](../chain-models/approximations/torus-test-map.md)
- [The torus](../chain-models/grid/torus.md)
- [The round sphere](../corner/round-sphere.md)
- [Fixed local data](../local-data/control/fixed-local-data.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [Finite-support subcategory](../categories/asymptotic/eventually-zero-subcategory.md)
- [Free category of a finite group](../categories/asymptotic/free-category.md)
- [Group sequence](../categories/asymptotic/group-sequence.md)
- [Point filtration](../categories/asymptotic/point-filtration.md)
- [Point category](../categories/asymptotic/point-quotient.md)
- [Sequence category](../categories/asymptotic/point-sequence-category.md)
- [The asymptotic category has finite biproducts](../categories/asymptotic/structure/biproducts.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [The support subcategory is additive](../categories/supports/support-dual-additive.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Bound sequence](../compression/bound-sequence.md)
- [Compressed complex](../compression/compressed-complex.md)
- [Compressed maps](../compression/compressed-maps.md)
- [Graph-type homotopy action](../corner/actions/graph-type-action.md)
- [The exterior](../corner/exterior.md)
- [Standing data](../corner/standing-data.md)
- [Forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md)
- [Scalar iterated cut](../corner/theorem/scalar-iterated-cut.md)
- [Cubical pinch](../evaluation/cubical-pinch.md)
- [The labelled-model class](../evaluation/germ.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)
- [Idempotent completion with duality](../l-theory/base/categories/karoubi-duality.md)
- [Embedding into the idempotent completion](../l-theory/base/categories/karoubi-embedding.md)
- [Group structure on L](../l-theory/base/groups/l-group-add.md)
- [L-group](../l-theory/base/groups/l-group.md)
- [The projective L-group](../l-theory/base/groups/projective-l-group.md)
- [Duality functors carry Poincaré complexes](../l-theory/base/pairs/functor-poincare.md)
- [Strict symmetric Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [The category of based ℚ-vector spaces](../l-theory/localization/products/bookkeeping/based-category.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [The class map](../l-theory/ultimate/groups/ultimate-cls.md)
- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)
- [The cyclic action on the control space](../local-data/control/control-action.md)
- [The metric on the control space](../local-data/control/control-metric-space.md)
- [The control space is compact](../local-data/control/control-space-compact.md)
- [The control space](../local-data/control/control-space.md)
- [The tail signature](../signatures/tail/tail-signature.md)
