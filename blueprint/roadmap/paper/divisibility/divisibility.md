---
article_id: af_dd8bcb4e5ca0dc1136e6e9cf
declaration: theorem
origin: bridged
---

# Divisibility of the signature tail

Let $X$ be a compact metric space with a free isometric $C_p$-action. For each $i$, let $\chi_i:G_i\to C_p$ be a surjection from a finite $p$-group. Each $G_i$ acts on $X$ through $\chi_i$, and labels are $G_i$-equivariant. Let $\Phi$ be the functor that forgets labels. Then for every $\alpha\in\mathbb L_4(\mathcal A_{\mathbf G}(X))$, every representative $(\sigma_i)$ of $\sigma_{\mathrm{tail}}(\Phi_*\alpha)\in\mathbb Z^{\mathbb N}/\mathbb Z^{(\mathbb N)}$ satisfies $p\mid\sigma_i$ for all sufficiently large $i$.

*Proof sketch.*
1. Take a trivializing closed cover of length $s$. Nilpotence gives $\nu^s\alpha=0$.
2. Write $\tau_{\mathcal P}$ for $\tau_{Q_i}$ in each coordinate, where $Q_i=G_i/\ker\chi_i$, and $\tau_{\mathcal V}$ for the functor it induces on $\mathcal V$. Then $\Phi\circ(\tau\otimes-)=\tau_{\mathcal V}\circ\Phi$ and $q\circ\tau_{\mathcal P}=\tau_{\mathcal V}\circ q$ hold strictly.
3. Lift $\Phi_*\alpha=q_*y$. Then $q_*\big((p-\tau_{\mathcal P})^s_*y\big)=\Phi_*(\nu^s\alpha)=0$. Lifts agree eventually, and cls is natural. So $x_i=\mathrm{cls}^{-1}(\pi_i)_*y$ satisfies $(p-\tau_{Q_i*})^sx_i=0$ in $L^p_4(\mathbb Q[G_i])$ for large $i$.
4. Choose $g_i$ with $\chi_i(g_i)\ne0$. Then $g_i$ fixes no coset in $Q_i$. By the permutation rule and additivity, $p^s\,\mathrm{Sign}(x_i)(g_i)=0$, so $\mathrm{Sign}(x_i)(g_i)=0$.
5. Because $\chi_i(g_i)\ne0$, we have $g_i\ne1$. Since $G_i$ is a $p$-group, $g_i$ has order $p^a$ with $a\ge1$. Let $H=\langle g_i\rangle$. By the restriction lemmas, $\mathrm{Sign}_H(\mathrm{res}\,x_i)(g_i)=\mathrm{Sign}(x_i)(g_i)=0$ and $\sigma_H(\mathrm{res}\,x_i)=\sigma_{G_i}(x_i)$. The cyclotomic lemma for $H$ gives $p\mid\sigma_{G_i}(x_i)$.
6. By the computation rule, $\sigma_{\mathrm{tail}}(\Phi_*\alpha)=[(\sigma_{G_i}(x_i))_i]$. Two representatives differ in finitely many terms.

## Sources

- HS paper, Section 4 (Integer tail divisibility).
- New: arbitrary finite $p$-groups, by restricting to $\langle g_i\rangle$.

## Depends on

- [Tail signature](../signatures/tail/tail-signature.md)
- [Forgetting labels](../categories/functors/forget-labels.md)

## Proof depends on

- [Trivializing closed cover](trivializing-cover.md)
- [Nilpotence](nu-nilpotent.md)
- [Classes over $\mathcal V$ lift](../signatures/tail/tail-lift.md)
- [Lifts agree eventually](../signatures/tail/tail-lift-eventual.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [Permutation rule on $L^p_4$](../signatures/l-four/signature-permutation.md)
- [Signature hom](../signatures/l-four/signature-hom.md)
- [Restriction of the signature](../signatures/l-four/signature-restrict.md)
- [Restriction of the integer signature](../signatures/l-four/integer-signature-restrict.md)
- [Cyclotomic lemma on $L^p_4$](../signatures/l-four/signature-cyclotomic.md)
- [Computing the tail signature](../signatures/tail/tail-signature-lift.md)
