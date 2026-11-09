---
declaration: lemma
origin: bridged
---
# The compressed complex is Poincaré

$(C,\hat d,\hat\varphi)$ is a strict $N$-dimensional symmetric Poincaré complex in $\mathcal B_{\mathbf 1,Z}(T\times S^n)$, concentrated in $[0,N]$. It has homotopy inverse $\hat b$ and homotopies $\hat H,\hat H'$.

*Proof sketch.* The maps $\hat\varphi,\hat b,\hat H,\hat H'$ are submatrices of type-$0$ elements of $\mathcal P_i$ on cells of $\mathcal B_i(u)$, so their propagation is at most $\delta_i\to0$; they are morphisms. [Residuals](compressed-residuals.md) (4) are exact. In (5)-(7), every term on the right is a type-$0$ endpoint word. It factors through the object $(W_i)$, which is supported in $Z$, by morphisms, so it vanishes in the [exterior quotient](../categories/exterior-quotient.md). A sum factors through the direct sum.

## Sources
- HS paper, Section 10 (compressed realization). New: symmetric over $\mathbb Q$, with no quadratic halving.
## Depends on
- [Compressed differential](compressed-differential.md), [compressed maps](compressed-maps.md), [strict Poincaré complex](../l-theory/A4.md)
## Proof depends on
- [Residuals](compressed-residuals.md), [endpoint lemma](endpoint-lemma.md), [support ideal](../categories/support-ideal.md)
