---
article_id: af_3921d1389770902612c57cf8
declaration: def
origin: bridged
statement: formalized
lean: HSP.relabelIso
---

# Relabelling isomorphism

Let $M=(n_i,x_i)$ and $M'=(n_i,x'_i)$ be objects with $\max_kd(x_i(k),x'_i(k))\to0$. The identity matrices give an isomorphism $f:M\to M'$ with $f^{*}=f^{-1}$.

*Proof sketch.* The labels of $(g,k)$ in $M$ and in $M'$ are $d(x_i(k),x'_i(k))$ apart, because the action is isometric. By [relabelling the propagation](../asymptotic/prop-relabel.md), the identity matrices have propagation at most this error, which tends to $0$. They are mutually inverse and self-transpose.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)

## Proof depends on

- [Relabelling changes propagation](../asymptotic/prop-relabel.md)
