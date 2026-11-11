---
article_id: af_c4e7b6f33c5d4611d8f3bab8
declaration: def
origin: bridged
---

# The permutation tensor on tails

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](../../categories/asymptotic/group-sequence.md), and let $\tau_{C_p}$ on $\mathrm{Free}(\mathbb Q[G_i])$ be [tensoring with the permutation module](permutation-tensor.md) of the $G_i$-set $C_p$, $g\cdot c=\chi_i(g)+c$, with $\varepsilon_{C_p}$ the identity of $C_p=\{0..p-1\}$, so that $C_p\times\{1..n\}$ is enumerated by the permutation enumeration $e_n(c,k)=c\,n+k$ of the [permutation tensor](../../categories/functors/tensor-permutation.md) of the asymptotic category. Let $\tau_{\mathcal P}=(\tau_{C_p})_i:\mathcal P_{\mathbf G}\to\mathcal P_{\mathbf G}$ be the product functor on the [sequence category](../../categories/asymptotic/point-sequence-category.md). $\tau_{\mathcal V}:\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf G}$ is the strict duality functor on the [point category](../../categories/asymptotic/point-quotient.md) that sends $(n_i)$ to $(p\,n_i)$ and $q(u_i)$ to $q(\tau_{C_p}u_i)$. Then $\tau_{\mathcal V}\circ q=q\circ\tau_{\mathcal P}$ and $\pi_i\circ\tau_{\mathcal P}=\tau_{C_p}\circ\pi_i$ hold strictly.

*Proof sketch.* (Well-definedness.) $\tau_{C_p}$ sends the zero object $0$ to $p\cdot0=0$ and the zero matrix to the zero matrix, so $\tau_{\mathcal P}$ keeps eventually zero sequences eventually zero. If $u_i=u'_i$ for all but finitely many $i$, then $\tau_{C_p}u_i=\tau_{C_p}u'_i$ for the same $i$, so by the [point ideal](../../categories/asymptotic/point-ideal.md) the classes agree. Composition, identities and transposes are preserved because each $\tau_{C_p}$ preserves them.

## Sources

- HS paper, Section 4

## Depends on

- [Tensoring with a permutation module](permutation-tensor.md)
- [Permutation tensor](../../categories/functors/tensor-permutation.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Sequence category](../../categories/asymptotic/point-sequence-category.md)
- [Point category](../../categories/asymptotic/point-quotient.md)

## Proof depends on

- [Point ideal](../../categories/asymptotic/point-ideal.md)
