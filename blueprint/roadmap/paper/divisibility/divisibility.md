---
article_id: af_dd8bcb4e5ca0dc1136e6e9cf
declaration: theorem
origin: bridged
---

# Divisibility of the signature tail

Let $X$ be a compact metric space with a free isometric $C_p$-action, and let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](../categories/asymptotic/group-sequence.md) in which every $G_i$ is a finite $p$-group and every $\chi_i:G_i\to C_p$ is onto. Let $\Phi:\mathcal A_{\mathbf G}(X)\to\mathcal V_{\mathbf G}$ be [forgetting labels](../categories/functors/forget-labels.md). Then for every $\alpha\in\mathbb L_4(\mathcal A_{\mathbf G}(X))$, every representative $(\sigma_i)$ of the [tail signature](../signatures/tail/tail-signature.md) $\sigma_{\mathrm{tail}}(\Phi_*\alpha)\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$ satisfies $p\mid\sigma_i$ for all sufficiently large $i$.

This rests on the open statements [Lemma U](../l-theory/comparison/lemma-u.md) and [lifting](../l-theory/localization/boundary/lift-to-pair.md), through the tail signature, and on lifting also through the excision boundary of the [support Mayer-Vietoris functor](support-mayer-vietoris.md). The groups $G_i$ are written additively, with neutral element $0$.

*Proof sketch.*
1. ($\nu^s=0$ on all of $\mathcal A_{\mathbf G}(X)$.) Take a [trivializing closed cover](trivializing-cover.md) of length $s$; [nilpotence](nu-nilpotent.md) gives $\nu_X^s=0$ on $\mathbb L_4(\mathcal A_X)$. Every object of $\mathcal A_{\mathbf G}(X)$ is $X$-supported, so the inclusion $\iota:\mathcal A_X\to\mathcal A_{\mathbf G}(X)$ and the functor back, both the identity on objects and morphisms, are inverse isomorphisms of duality categories, and $\iota_*$ is bijective by [equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md). Since $\nu_X=p-(\tau|_{\mathcal A_X})_*$ and $\iota\circ\tau|_{\mathcal A_X}=(\tau\otimes-)\circ\iota$ strictly, [functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md) gives $(p-(\tau\otimes-)_*)^s\alpha=\iota_*\nu_X^s\beta=0$ for $\alpha=\iota_*\beta$.
2. (Commuting with $\Phi$.) Let $\tau_{\mathcal P}$, $\tau_{\mathcal V}$ and $\tau_{C_p}$ be as in [the permutation tensor on tails](../signatures/point-functors/tail-permutation-functor.md). Then $\Phi\circ(\tau\otimes-)=\tau_{\mathcal V}\circ\Phi$ strictly: both send $(n_i,x_i)$ to $(p\,n_i)$, and on morphisms the matrix of the [permutation tensor](../categories/functors/tensor-permutation.md) is, entry for entry, the explicit matrix of [$\tau_{C_p}$](../signatures/point-functors/permutation-tensor.md), because both index $C_p\times\{1..n_i\}$ by the permutation enumeration $e_{n_i}(c,k)=c\,n_i+k$ of the permutation tensor.
3. (Lifting.) [Lift](../signatures/tail/tail-lift.md) $\Phi_*\alpha=q_*y$. By functoriality, step 2 and $\tau_{\mathcal V}q=q\tau_{\mathcal P}$, $q_*\big((p-(\tau_{\mathcal P})_*)^sy\big)=\Phi_*\big((p-(\tau\otimes-)_*)^s\alpha\big)=0$. By [eventual agreement](../signatures/tail/tail-lift-eventual.md) and $\pi_i\tau_{\mathcal P}=\tau_{C_p}\pi_i$, $(p-(\tau_{C_p})_*)^s(\pi_i)_*y=0$ for large $i$. Put $x_i=\mathrm{cls}^{-1}(\pi_i)_*y\in L^p_4(\mathrm{Free}(\mathbb Q[G_i]))$, with cls bijective by the [point comparison](../l-theory/comparison/free-comparison.md). Since [cls commutes with induced maps](../l-theory/ultimate/groups/induced-map-cls.md), $(p-(\tau_{C_p})_*)^sx_i=0$ for large $i$.
4. (Vanishing character.) Choose $g_i$ with $\chi_i(g_i)\ne0$. It acts on $C_p$ by a nonzero translation, so it fixes no point. By the [permutation rule](../signatures/l-four/signature-permutation.md), $\mathrm{Sign}_{G_i}((\tau_{C_p})_*z)(g_i)=0$ for every $z$, and since [$\mathrm{Sign}_{G_i}$ is additive](../signatures/l-four/signature-hom.md), $0=\mathrm{Sign}_{G_i}((p-(\tau_{C_p})_*)^sx_i)(g_i)=p^s\,\mathrm{Sign}_{G_i}(x_i)(g_i)$. So $\mathrm{Sign}_{G_i}(x_i)(g_i)=0$.
5. (Restriction.) Since $\chi_i(g_i)\ne0$, $g_i\ne0$. Since $G_i$ is a $p$-group, $g_i$ has order $p^a$ with $a\ge1$. Let $H=\langle g_i\rangle$. By [restriction on $L^p_4$](../signatures/l-four/signature-restrict.md), $\mathrm{Sign}_H(\mathrm{res}\,x_i)(g_i)=\mathrm{Sign}_{G_i}(x_i)(g_i)=0$, and by [restriction of the integer signature](../signatures/l-four/integer-signature-restrict.md), $\sigma_H(\mathrm{res}\,x_i)=\sigma_{G_i}(x_i)$. The [cyclotomic lemma](../signatures/l-four/signature-cyclotomic.md) for $H$ gives $p\mid\sigma_{G_i}(x_i)$.
6. By the [computation rule](../signatures/tail/tail-signature-lift.md), $\sigma_{\mathrm{tail}}(\Phi_*\alpha)=[(\sigma_{G_i}(x_i))_i]$. Two representatives differ in finitely many terms.

## Sources

- HS paper, Section 4 (Integer tail divisibility).
- New: arbitrary finite $p$-groups, by restricting to $\langle g_i\rangle$.

## Depends on

- [Group sequence](../categories/asymptotic/group-sequence.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Forgetting labels](../categories/functors/forget-labels.md)
- [Tail signature](../signatures/tail/tail-signature.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)

## Proof depends on

- [Trivializing closed cover](trivializing-cover.md)
- [Nilpotence](nu-nilpotent.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [Permutation tensor](../categories/functors/tensor-permutation.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
- [The permutation tensor on tails](../signatures/point-functors/tail-permutation-functor.md)
- [Tensoring with a permutation module](../signatures/point-functors/permutation-tensor.md)
- [Classes over $\mathcal V$ lift](../signatures/tail/tail-lift.md)
- [Lifts agree eventually](../signatures/tail/tail-lift-eventual.md)
- [Point comparison for the free categories](../l-theory/comparison/free-comparison.md)
- [The induced map commutes with cls](../l-theory/ultimate/groups/induced-map-cls.md)
- [Permutation rule on $L^p_4$](../signatures/l-four/signature-permutation.md)
- [The equivariant signature on $L^p_4$](../signatures/l-four/signature-hom.md)
- [Restriction on $L^p_4$](../signatures/l-four/signature-restrict.md)
- [Restriction keeps the integer signature](../signatures/l-four/integer-signature-restrict.md)
- [Cyclotomic lemma on $L^p_4$](../signatures/l-four/signature-cyclotomic.md)
- [Computing the tail signature](../signatures/tail/tail-signature-lift.md)
