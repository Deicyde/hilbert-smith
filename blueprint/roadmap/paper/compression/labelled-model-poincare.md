---
declaration: lemma
origin: bridged
---
# Labelled models are Poincaré

Let $\mathbf k=(k_i)$ be integers with $k_i\ge3$ and $k_i\to\infty$, and let $c:T^n\to S^n$ be continuous. Label each cell $b$ of $D(k_i)=C(k_i)\otimes P$ by $c(x_b)$. With the [duality data](../chain-models/chain-model-duality.md), $(D(k_i),d,\varphi)$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal A_{\mathbf 1}(S^n)$. Its image in $\mathcal B_{\mathbf 1,Z_0}(S^n)$ is one too.

*Proof sketch.* The identities of the [Poincaré theorem](../chain-models/chain-model-poincare.md) hold for each $k\ge3$. The torus propagation of $d,\varphi,b,H,H'$ is at most $4/k_i$, so the sphere propagation is at most $\omega_c(4/k_i)\to0$ by uniform continuity. The quotient functor preserves duality.

## Depends on
- [Chain-model duality](../chain-models/chain-model-duality.md), [strict Poincaré complex](../l-theory/A4.md), [exterior quotient](../categories/exterior-quotient.md)
## Proof depends on
- [Poincaré](../chain-models/chain-model-poincare.md), [functors induce maps](../l-theory/A10.md)
