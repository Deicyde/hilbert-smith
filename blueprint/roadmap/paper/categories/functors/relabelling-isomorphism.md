---
article_id: af_3921d1389770902612c57cf8
declaration: def
origin: bridged
statement: formalized
lean: HSP.relabelIso
---

# Relabelling isomorphism

Suppose the $C_p$-action on $X$ is isometric. Let $M=(n_i,x_i)$ and $M'=(n_i,x'_i)$ be objects with $\max_kd(x_i(k),x'_i(k))\to0$. The identity matrices give an isomorphism $f:M\to M'$ with $f^{*}=f^{-1}$.

These isomorphisms are natural: if $u:M\to N$ and $u':M'\to N'$ have the same matrices, where $N=(m_i,y_i)$ and $N'=(m_i,y'_i)$ with $\max_kd(y_i(k),y'_i(k))\to0$, then $[u']\circ f_M=f_N\circ[u]$, because every component of $f$ is an identity matrix.

*Proof sketch.* The labels of $(g,k)$ in $M$ and in $M'$ are $d(x_i(k),x'_i(k))$ apart, because the action is isometric. By [relabelling the propagation](../asymptotic/prop-relabel.md), the identity matrices have propagation at most this error, which tends to $0$. They are mutually inverse and self-transpose.

## Sources

- HS paper, Section 2

## Depends on

- [Asymptotic duality](../asymptotic/asymptotic-duality.md)

## Proof depends on

- [Propagation of the identity](../asymptotic/prop-one.md)
- [Relabelling changes propagation](../asymptotic/prop-relabel.md)
