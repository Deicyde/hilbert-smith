---
article_id: af_53157d399fbd94f85df27e30
declaration: def
origin: background
---

# Support collapse

For $M\in H_b$, let $\rho(M)$ be the least $R\in\mathbb N$ such that $M_n$ is a zero object whenever $|n|>R$. Put $\sigma(M)=\bigoplus_{|n|\le\rho(M)}M_n$. For $f:M\to N$, let $\sigma(f)$ be the matrix $(f_{mn})$ with $|m|\le\rho(N)$ and $|n|\le\rho(M)$. Then $\sigma:H_b\to D$ is a functor, and with $\xi_M:\sigma(M^*)\to\sigma(M)^*$ the canonical isomorphism $\bigoplus_nM_n^*\cong(\bigoplus_nM_n)^*$ it is a duality functor.

*Proof sketch.* Since $\rho(M^*)=\rho(M)$, both sides of $\xi_M$ run over the same window. $\sigma(gf)=\sigma(g)\sigma(f)$ holds because the entries of $N$ outside its window are zero objects, so dropping them from $\sum_mg_{lm}f_{mn}$ does not change the sum. $\xi_M^*=\xi_{M^*}$ holds entrywise.

## Sources

- New: the total object over the least support window.

## Depends on

- [Half-line subcategories](half-lines.md)
- [Duality functor](../../base/categories/duality-functor.md)
