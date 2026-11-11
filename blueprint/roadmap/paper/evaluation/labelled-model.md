---
article_id: af_4771ee01ff5de0bc3a416bbb
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Evaluation.labelledModel_poincare
---
# The labelled chain model is Poincaré

Let $c:\mathbb T^n\to S^n$ be continuous. Give the basis cell $b$ of $D_i$ (and its dual) the label $c(x_b)$. Then $(D_i,\varphi_i)_i$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal A_{\mathbf 1}(S^n)$, concentrated in $[0,N]$. Its inverse is $b_i$, with homotopies $H_i$ ([the homotopy of the chain model](../chain-models/grid/poincare/chain-model-h.md)) and $H'_i$ ([the dual homotopy](../chain-models/grid/poincare/chain-model-h-dual.md)).

*Proof sketch.* $d^2=0$, $T\varphi_i=\varphi_i$ and the homotopy identities hold exactly ([Poincaré](../chain-models/grid/chain-model-poincare.md) (1), (2)). In torus labels, $d$ has $d_\infty$-propagation at most $h_i/2$ ([propagation of the differential](../chain-models/grid/poincare/chain-model-d-propagation.md)), and $\varphi_i,b_i,H_i,H'_i$ have propagation at most $h_i$ (item 3). With the modulus $\omega_c$ of $c$ for $d_S$, the sphere propagation is at most $\omega_c(h_i)\to0$.

## Sources
- HS paper, Section 12 (labellings by a continuous map).
## Depends on
- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [Chain model](../chain-models/grid/model/chain-model.md)
- [Chain-model duality](../chain-models/grid/chain-model-duality.md)
- [The homotopy of the chain model](../chain-models/grid/poincare/chain-model-h.md)
- [The dual homotopy of the chain model](../chain-models/grid/poincare/chain-model-h-dual.md)
- [Strict Poincaré complex](../l-theory/base/pairs/symmetric-poincare-complex.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [The chain model is Poincaré](../chain-models/grid/chain-model-poincare.md)
## Proof depends on
- [Poincaré](../chain-models/grid/chain-model-poincare.md)
- [Propagation](../categories/asymptotic/propagation.md)
- [The torus](../chain-models/grid/torus.md)
- [The round sphere](../corner/round-sphere.md)
- [Group sequence](../categories/asymptotic/group-sequence.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [Dual complex](../l-theory/base/complexes/dual-complex.md)
- [Duality map of a cycle](../l-theory/base/complexes/cycle-chain-map.md)
- [Propagation of the differential of the chain model](../chain-models/grid/poincare/chain-model-d-propagation.md)
