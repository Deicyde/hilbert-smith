---
article_id: af_4771ee01ff5de0bc3a416bbb
declaration: lemma
origin: bridged
---
# The labelled chain model is Poincaré

Let $c:T^n\to S^n$ be continuous. Give the basis cell $b$ of $D_i$ (and its dual) the label $c(x_b)$. Then $(D_i,\varphi_i)_i$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal A_{\mathbf 1}(S^n)$, concentrated in $[0,N]$. Its inverse is $b_i$, with homotopies $H_i,H'_i$.

*Proof sketch.* $d^2=0$, $T\varphi_i=\varphi_i$ and the homotopy identities hold exactly ([Poincaré](../chain-models/grid/chain-model-poincare.md) (1), (2)). In torus labels, $d$ has $d_\infty$-propagation at most $h_i/2$, and $\varphi_i,b_i,H_i,H'_i$ have propagation at most $h_i$ (item 3). With the modulus $\omega_c$ of $c$ for $d_S$, the sphere propagation is at most $\omega_c(h_i)\to0$.

## Sources
- HS paper, Section 12 (labellings by a continuous map).
## Depends on
- [Chain model](../chain-models/grid/chain-model.md), [chain-model duality](../chain-models/grid/chain-model-duality.md), [strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md), [asymptotic category](../categories/asymptotic/asymptotic-category.md)
## Proof depends on
- [Poincaré](../chain-models/grid/chain-model-poincare.md), [propagation](../categories/asymptotic/propagation.md)
