---
declaration: lemma
origin: bridged
---
# Compressed differential

$\hat d^2=0$ and $\mathrm{pr}_i\,d=\hat d\,\mathrm{pr}_i$. Also $\operatorname{prop}(\hat d)\le\delta_i$ in $T\times S^n$, so $(C,\hat d)$ is a chain complex in $\mathcal A_{\mathbf 1}(T\times S^n)$, concentrated in $[0,N]$.

*Proof sketch.* $\mathrm{pr}\,d=\mathrm{pr}\,d(\mathrm{in}\,\mathrm{pr}+Q)=\hat d\,\mathrm{pr}$ by the [subcomplex](discarded-subcomplex.md) identity. Then $\hat d^2=\mathrm{pr}\,d^2\,\mathrm{in}=0$. $\hat d$ is a submatrix of $d$ on cells of $\mathcal B_i(u)$, and graph type $0$ with bound $\delta$ means propagation at most $\delta$.

## Depends on
- [Compressed complex](compressed-complex.md)
## Proof depends on
- [Discarded subcomplex](discarded-subcomplex.md), [buffers](buffer-eventually.md)
