---
article_id: af_b399c5dee7fa7712c7ab9415
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.relabelIso_natural
---

# The relabelling isomorphism is natural

In the setting of the [relabelling isomorphism](relabelling-isomorphism.md), let $M=(n_i,x_i)$, $M'=(n_i,x'_i)$, $N=(m_i,y_i)$ and $N'=(m_i,y'_i)$ with $\max_kd(x_i(k),x'_i(k))\to0$ and $\max_kd(y_i(k),y'_i(k))\to0$. If $u:M\to N$ and $u':M'\to N'$ have the same matrices, then $[u']\circ f_M=f_N\circ[u]$.

*Proof sketch.* Every component of $f_M$ and $f_N$ is an identity matrix, so both composites have the matrices of $u$.

## Sources

- HS paper, Section 2

## Depends on

- [Relabelling isomorphism](relabelling-isomorphism.md)
