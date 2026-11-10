---
article_id: af_9826c6c5fb5c31668271cb17
declaration: def
origin: background
---

# Dual of a tensor product

Let $C$ and $E$ be as in [Tensor product of complexes over the line](complex-product.md), let $m,n\in\mathbb Z$, $N=m+n$ and $s(a,b)=(-1)^{b(a+m)}$. The isomorphism of complexes
$$\Xi:(C\otimes E)^{N-*}\to C^{m-*}\otimes E^{n-*}$$
is $s(a,b)$ times $\kappa$ ([Duals of box products](box-dual.md)) on the summand $(C_{m-a}\boxtimes E_{n-b})^*$, which it carries to $C^*_{m-a}\boxtimes E^*_{n-b}$ in position $(a,b)$.

*Proof sketch.* (It is a chain map.) In position $(a,b)$, the differential of $(C\otimes E)^{N-*}$ has components $(-1)^{a+b}d^*\boxtimes1$ to $(a-1,b)$ and $(-1)^{b+m}1\boxtimes d^*$ to $(a,b-1)$; that of $C^{m-*}\otimes E^{n-*}$ has $(-1)^ad^*\boxtimes1$ and $(-1)^{a+b}1\boxtimes d^*$ ([Dual complex](../../base/complexes/dual-complex.md)). The identities $s(a-1,b)=(-1)^bs(a,b)$ and $s(a,b-1)=(-1)^{a+m}s(a,b)$ are exactly the chain-map condition. Each component is an isomorphism, so $\Xi$ is one.

## Sources

- [Ranicki 1980 I, §8](../../../../../sources/paper/ranicki-1980.md) [U]
- New: the signs in this paper's conventions.

## Depends on

- [Tensor product of complexes over the line](complex-product.md)
- [Duals of box products](box-dual.md)
- [Dual complex](../../base/complexes/dual-complex.md)
