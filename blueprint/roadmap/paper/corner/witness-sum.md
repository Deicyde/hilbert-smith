---
declaration: lemma
origin: bridged
---

# Sums of witnesses

Let $K$ be a finite set and, for $k\in K$, let $e_k:M_k\to M'_k$ be an exterior witness of type $c$ with bound $\delta$ through $W_k$. Let $a_k:M'_k\to M'$ and $b_k:M\to M_k$ have propagation $0$, and let $\lambda_k\in\mathbb Q$. Then $\sum_k\lambda_ka_ke_kb_k$ is an exterior witness of type $c$ with bound $\delta$ through $\bigoplus_kW_k$.

*Proof sketch.* With $e_k=x_ky_k$, the first factor is the column $(y_kb_k)_k$ and the second is the row $(\lambda_ka_kx_k)_k$. Composing with propagation $0$ keeps the graph type and the bound ([Propagation bounds](../categories/propagation-bounds.md)), and a row or column has the maximum of its entries' bounds.

## Sources

- New: the stacked witness; its bound does not depend on $|K|$.

## Depends on

- [Exterior witnesses](exterior-witness.md)

## Proof depends on

- [Propagation bounds](../categories/propagation-bounds.md)
