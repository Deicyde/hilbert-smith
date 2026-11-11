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
2. Otherwise suppose the action is faithful. $O$ is a connected $n$-manifold, so it carries fixed local data with $D=1/64$, with buffer radius $R$, control space $T$ (possibly empty) and torus test map $f_T$. Fix $s=R/(2\sqrt n)$, so $0<s<R/\sqrt n$, and let $G_i=\mathbb Z/p^{\max(i,1)}$ for $i\in\mathbb N$, with $\chi_i$ reduction modulo $p$, so that every $\chi_i$ is onto (level $0$ carries nothing, since the compressed complex vanishes below its start index $i_0\ge1$). Let $Z_0$ be the [exterior](../corner/exterior.md) for $n$ and $R$, $Z=T\times Z_0$, and let $\Delta_{\mathbf 1}$ be the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) for this $n$, $R$ and $s$; it needs no control space, and both Theorem B (step 3) and Theorem A (step 6) are applied to this $\Delta_{\mathbf 1}$.
3. The torus test map is continuous, as the start of a continuous homotopy to the cubical pinch ([the torus test map is homotopic to the cubical pinch](../evaluation/test-map-to-pinch.md)). Theorem B for the test map, with this $s$, gives $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})=[(\varepsilon,\varepsilon,\dots)]$ with $\varepsilon\in\{\pm1\}$, for the [labelled-model class](../evaluation/germ.md) $\mathfrak m_{f_T}$.
4. Theorem C gives the compressed complex $(C,\hat\varphi)$, a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$ concentrated in $[0,N]$ (clause 1), with $U'_*\operatorname{cls}(C,\hat\varphi)=\mathfrak m_{f_T}$ (clause 3), where $U'$ is [forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md) for $T$, $R$ and the trivial group sequence, and $\operatorname{cls}(C,\hat\varphi)$ is $\operatorname{cls}$ of the image of $(C,\hat\varphi)$ under the [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md) $M\mapsto(M,1)$.
5. Case $T=\varnothing$. Then $T\times S^n$ is empty, so every object of the asymptotic category over it, and hence every chain object of $C$, is a zero object. The chain map from $C$ to the zero complex is an isomorphism carrying $\hat\varphi$ to $0$, so $[C,\hat\varphi]=0$ by homotopy-isometry invariance, and $\operatorname{cls}(C,\hat\varphi)=0$ ([the class over an empty space vanishes](empty-control-class.md)). By step 4, $\mathfrak m_{f_T}=U'_*0=0$. As $\Delta_{\mathbf 1}$ (a composite of induced maps, cut boundaries and inverses of induced isomorphisms) and $\sigma_{\mathrm{tail}}$ are homomorphisms, step 3 gives $[(\varepsilon,\varepsilon,\dots)]=0$, so $\varepsilon=0$ for all large $i$, which is false.
6. Case $T\ne\varnothing$. By Theorem C (clause 2), $p$, $(G_i,\chi_i)$, $T$, $n$, $R$ and $s$ form standing data (the [standing data of the compression](../compression/compressed-standing-data.md)), and $(C,\hat\varphi)$ carries a graph-type homotopy action of $\mathbf G=(G_i,\chi_i)$. Theorem A, applied to $(C,\hat\varphi)$, says that every representative of $\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}U'_*\operatorname{cls}(C,\hat\varphi))=\sigma_{\mathrm{tail}}(\Delta_{\mathbf 1}\mathfrak m_{f_T})$ is eventually divisible by $p$. By step 3, $(\varepsilon,\varepsilon,\dots)$ is such a representative. The lemma on integer tails, for the constant sequence $\varepsilon$, gives a contradiction.

This proof rests on the open statements [Newman's theorem on fixing an open set](../inputs/newman/newman-open-set.md) (through the fixed local data), [lifting](../l-theory/localization/boundary/lift-to-pair.md) (through every cut boundary and the tail signature), [the two sides of an excision boundary](../l-theory/ultimate/boundary/excision-boundary-swap.md) (through the inner cuts of Theorem B), [Lemma U](../l-theory/comparison/lemma-u.md) (through the tail signature) and [idempotent splitting in the bounded homotopy category](../corner/theorem/kb-idempotent-splitting.md) (through Theorem A).

## Sources

- [HS paper, Section 13](../../../sources/hs-paper.md#section-13-the-contradiction-seccontradiction-lines-1326-1391) (Proposition 13.1 and the proof of Theorem 1.1)
- [HS paper, Section 4](../../../sources/hs-paper.md#section-4-divisibility-over-a-free-c_p-space-algobstruction-lines-317-380)
- New: the contradiction is assembled from Theorems A, B and C as stated in this paper, with $T$ the control space of the fixed local data

## Depends on

## Proof depends on

- [Fixed local data from a faithful action](../local-data/control/fixed-local-data-exists.md)
- [Standing data](../corner/standing-data.md)
- [Standing data of the compression](../compression/compressed-standing-data.md)
- [The exterior](../corner/exterior.md)
- [Scalar iterated cut](../corner/theorem/scalar-iterated-cut.md)
- [Forgetting to the scalar exterior quotient](../corner/theorem/scalar-forget.md)
- [The labelled-model class](../evaluation/germ.md)
- [Karoubi embedding](../l-theory/base/categories/karoubi-embedding.md)
- [Theorem B for the test map](../evaluation/theorem-b-test-map.md)
- [The torus test map is homotopic to the cubical pinch](../evaluation/test-map-to-pinch.md)
- [Theorem C](../compression/theorem-c.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Exterior quotient](../categories/supports/exterior-quotient.md)
- [Homotopy-isometry invariance](../l-theory/base/groups/homotopy-isometry-invariance.md)
- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [The tail signature](../signatures/tail/tail-signature.md)
- [Theorem A](../corner/theorem/theorem-a.md)
- [Integer tails](integer-tails.md)
- [The class over an empty space vanishes](empty-control-class.md)
