---
declaration: def
origin: bridged
---

# Relabelling equivalence

Let $S\subset X$ be nonempty, closed and invariant. Fix $\rho:X\to S$ with $d(x,\rho x)=d(x,S)$. The relabelling equivalence consists of the following data:
- $P:\mathcal A_{\mathbf G}(S)\to\mathcal A_S$, the [pushforward](pushforward.md) along $S\hookrightarrow X$, corestricted;
- $R:\mathcal A_S\to\mathcal A_{\mathbf G}(S)$ with $R(n_i,x_i)=(n_i,\rho\circ x_i)$ and $R[u]=[u]$;
- $RP=\mathrm{id}$ on the nose;
- the counit $PR(M)\to M$, given by the [relabelling isomorphism](relabelling-isomorphism.md).

*Proof sketch.* $\rho$ fixes $S$ pointwise, since $d(s,\rho s)=0$, so $RP=\mathrm{id}$. Write $\varepsilon_i(M)=\max_kd(x_i(k),S)$. It tends to $0$ for $M\in\mathcal A_S$, and by isometry it bounds the label errors of $R(M)$. By [relabelling the propagation](prop-relabel.md), $\operatorname{prop}(Ru_i)\le\operatorname{prop}(u_i)+\varepsilon_i(M)+\varepsilon_i(N)\to0$. So $R$ is well defined, and it is a strict duality functor because the matrices are unchanged. $\rho$ need not be equivariant, because labels are $\chi_i(g)\rho(x_i(k))$. The counit is natural and unitary, and the triangle identities hold, because every component is an identity matrix.

## Sources

- HS paper, Section 2

## Depends on

- [Pushforward](pushforward.md)
- [Support subcategory](support-subcategory.md)

## Proof depends on

- [Relabelling changes propagation](prop-relabel.md)
- [Relabelling isomorphism](relabelling-isomorphism.md)
