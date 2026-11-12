---
article_id: af_04164e37933ca6b13008b334
declaration: def
origin: bridged
statement: formalized
lean: HSP.relabelEquiv
---

# Relabelling equivalence

Let $S\subset X$ be nonempty, closed and invariant. Fix $\rho:X\to S$ with $d(x,\rho x)=d(x,S)$. The relabelling equivalence consists of the following data:
- $P:\mathcal A_{\mathbf G}(S)\to\mathcal A_S$, the [pushforward](pushforward.md) along $S\hookrightarrow X$, corestricted;
- $R:\mathcal A_S\to\mathcal A_{\mathbf G}(S)$ with $R(n_i,x_i)=(n_i,\rho\circ x_i)$ and $R[u]=[u]$;
- $RP=\mathrm{id}$ on the nose;
- the counit $PR(M)\to M$, given by the [relabelling isomorphism](relabelling-isomorphism.md).

$\mathcal A_S$ is a duality category as a [dual subcategory](../../l-theory/base/categories/dual-subcategory.md), $P$ and $R$ are strict duality functors, and the identity $\mathrm{id}\cong RP$ and the counit $PR\cong\mathrm{id}$ are [unitary natural isomorphisms](../../l-theory/base/categories/unitary-isomorphism.md).

Given $\rho$, the construction does not need $S$ to be nonempty; the functor $R$ needs neither that $S$ is closed nor that $X$ is compact.

**Remark (not formalized).** Such a $\rho$ exists: $S$ is a nonempty closed subset of the compact space $X$, hence compact, so for every $x$ the distance $d(x,S)$ is attained at a point of $S$, and $\rho$ chooses one such point for each $x$.

**Remark (not formalized).** The triangle identities $\varepsilon_{P}\circ P\eta=\mathrm{id}_P$ and $R\varepsilon\circ\eta_R=\mathrm{id}_R$ hold, because every component is an identity matrix. They are not part of the data listed above.

*Proof sketch.* $\rho$ fixes $S$ pointwise, since $d(s,\rho s)=0$, so $RP=\mathrm{id}$. Write $\varepsilon_i(M)=\max_kd(x_i(k),S)$. It tends to $0$ for $M\in\mathcal A_S$, and by isometry it bounds the label errors of $R(M)$. By [relabelling the propagation](../asymptotic/prop-relabel.md), $\operatorname{prop}(Ru_i)\le\operatorname{prop}(u_i)+\varepsilon_i(M)+\varepsilon_i(N)\to0$. So $R$ is well defined, and it is a strict duality functor because the matrices are unchanged. $\rho$ need not be equivariant, because labels are $\chi_i(g)\rho(x_i(k))$. The counit is [natural](relabelling-isomorphism-natural.md) and [unitary](relabelling-isomorphism-unitary.md) because every component is an identity matrix; the unit is the identity, given by $RP=\mathrm{id}$.

## Sources

- HS paper, Section 2

## Depends on

- [Pushforward](pushforward.md)
- [Support subcategory](../supports/support-subcategory.md)
- [The support subcategory is additive](../supports/support-dual-additive.md)
- [Dual subcategory](../../l-theory/base/categories/dual-subcategory.md)
- [Unitary natural isomorphism](../../l-theory/base/categories/unitary-isomorphism.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)

## Proof depends on

- [Relabelling changes propagation](../asymptotic/prop-relabel.md)
- [Relabelling isomorphism](relabelling-isomorphism.md)
- [The relabelling isomorphism is unitary](relabelling-isomorphism-unitary.md)
- [The relabelling isomorphism is natural](relabelling-isomorphism-natural.md)
- [The levelwise transpose](../asymptotic/structure/levelwise-transpose.md)
- [Morphisms have propagation tending to zero](../asymptotic/structure/morphism-propagation.md)
- [Every morphism is a class](../asymptotic/structure/class-surjective.md)
- [Equality of classes](../asymptotic/structure/class-eq.md)
