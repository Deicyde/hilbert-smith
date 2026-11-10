---
article_id: af_2c4c5b590d2e388c3dfae5f6
declaration: theorem
origin: cited
---

# Lemma U (open statement)

Let $\mathbf G$ be a [group sequence](../../categories/asymptotic/group-sequence.md) and $\mathcal S_{\mathbf G}$ its [finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md). For every $j\ge1$ and every object $P$ of $\mathrm{Kar}\,C_{\mathbb Z^j}(\mathcal S_{\mathbf G})$ there are objects $F,F'$ of $C_{\mathbb Z^j}(\mathcal S_{\mathbf G})$ with $P\oplus F\cong F'$.

**Remark (not formalized).** This is an open statement: the Lean states it now and proves it later. By the [stable criterion](../bounded/categories/lower-k-vanishing-criterion.md) it says $K_{-j}(\mathcal S_{\mathbf G})=0$ for $j\ge1$. Planned route. (1) Morphisms of $\mathcal P_{\mathbf G}=\prod_i\mathrm{Free}(\mathbb Q[G_i])$ are sequences of matrices, so an object of $C_{\mathbb Z^j}(\mathcal S_{\mathbf G})$ and an idempotent on it split into coordinates $i$, each an object and idempotent of $C_{\mathbb Z^j}(\mathrm{Free}(\mathbb Q[G_i]))$ with propagation bounded independently of $i$. (2) Each $\mathbb Q[G_i]$ is semisimple by Maschke, hence regular noetherian, so its lower K-groups vanish, and bounded lower K agrees with Bass's lower K for rings ([Pedersen-Weibel 1985](../../../../sources/paper/pedersen-weibel-1985.md) [U]; [Schlichting 2006](../../../../sources/paper/schlichting-2006.md) [U]). This solves $P_i\oplus F_i\cong F'_i$ for each $i$ separately. (3) The gap: the solutions must have propagation bounded uniformly in $i$, and at each position of $\mathbb Z^j$ only finitely many $F_i$, $F'_i$ may be nonzero. Bass's finite-block argument does not transfer, because an object of $C_{\mathbb Z}(\mathcal S_{\mathbf G})$ may meet infinitely many blocks.

## Sources

- [Schlichting 2006, negative K-theory of noetherian abelian categories vanishes](../../../../sources/paper/schlichting-2006.md) [U] (candidate)
- [Pedersen-Weibel 1985, bounded and Bass lower K agree for rings](../../../../sources/paper/pedersen-weibel-1985.md) [U] (candidate)

## Depends on

- [Iterated bounded categories](../bounded/categories/iterated-bounded-category.md)
- [Idempotent completion with duality](../base/categories/karoubi-duality.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md)
