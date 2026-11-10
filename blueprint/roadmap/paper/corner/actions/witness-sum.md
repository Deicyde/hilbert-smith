---
article_id: af_1ef1cd6459d61f82ba4c0177
declaration: lemma
origin: bridged
---

# Sums of witnesses

Let $K$ be a finite set, possibly empty, and, for $k\in K$, let $e_k:M_k\to M'_k$ be an exterior witness of type $c$ with bound $\delta$ through $W_k$. Let $a_k:M'_k\to M'$ and $b_k:M\to M_k$ have propagation $0$, and let $\mu_k\in\mathbb Q$. Then $\sum_k\mu_ka_ke_kb_k$ is an exterior witness of type $c$ with bound $\delta$ through $\bigoplus_kW_k$.

*Proof sketch.* If $K$ is empty, the sum is the zero matrix, which factors through the zero module $\bigoplus_{k\in\varnothing}W_k$ by zero matrices; these have graph type $0$ and $c$ with any bound, since they have no nonzero entries. Otherwise, with $e_k=x_ky_k$, the first factor is the column $y=\sum_k\iota_ky_kb_k:M\to\bigoplus_kW_k$ and the second is the row $x=\sum_k\mu_ka_kx_k\pi_k$, where the inclusions $\iota_k$ and projections $\pi_k$ have propagation $0$. Each term $\iota_ky_kb_k$ has graph type $0$ with bound $\delta$, and each $\mu_ka_kx_k\pi_k$ has graph type $c$ with bound $\delta$ ([Calculus of graph types](graph-type-calculus.md), item 1 with propagation-$0$ factors; a scalar multiple has no new nonzero entries). Item 3 bounds the sums. Every label of $\bigoplus_kW_k$ is a label of some $W_k$.

## Sources

- New: the stacked witness; its bound does not depend on $|K|$.

## Depends on

- [Exterior witnesses](exterior-witness.md)

## Proof depends on

- [Calculus of graph types](graph-type-calculus.md)
