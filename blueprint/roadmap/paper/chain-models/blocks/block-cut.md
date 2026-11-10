---
article_id: af_c7cfb2022867fe0429f35feb
declaration: lemma
origin: background
---
# Block cut

Let $F_j=I_m$ be an arc factor of a [block](block-pair.md) $Q$ and $0<w<m$. Let $Q',Q''$ be the blocks with $F_j$ replaced by the subarcs on $[0],\dots,[w]$ and on $[w],\dots,[m]$ (the latter renumbered from $0$), with based inclusions $\iota':Q'\to Q$ and $\iota'':Q''\to Q$. Let $Q^\circ$ be $Q$ with $F_j$ replaced by the point $\mathbb Q[w]$, which is the top face of $Q'$ at position $j$ and the bottom face of $Q''$ there. Then:
1. $\varphi_Q=\iota'_\%\varphi_{Q'}+\iota''_\%\varphi_{Q''}$;
2. the summand of $\varphi_{\partial Q'}$ at its face $Q^\circ$ is $(-1)^{a_j}(\kappa'_j)_\%\varphi_{Q^\circ}$, and the summand of $\varphi_{\partial Q''}$ at $Q^\circ$ is $-(-1)^{a_j}(\kappa''_j)_\%\varphi_{Q^\circ}$, where $\kappa'_j,\kappa''_j$ are the face inclusions.

*Proof sketch.* (1) By [pushforward of products](../../l-theory/localization/products/product-push.md) it suffices to check one arc: $\varphi_I([w]^*)=\tfrac12e_{w-1}+\tfrac12e_w$ splits between the two subarcs, and every other entry lies in exactly one of them. (2) $[w]$ is the top end of the first subarc and the bottom end of the second, so $\varphi_C([w]^*)$ is $+[w]$ in one and $-[w]$ in the other. Replacing a factor structure by the point structure $1$ at position $j$ changes no other block sign, because a point has dimension and degree $0$.

## Sources
- New. Replaces the union lemma of HS paper, Section 12.
## Depends on
- [Block pair](block-pair.md), [pushforward of structures](../../l-theory/base/complexes/structure-push.md)
## Proof depends on
- [Pushforward of products](../../l-theory/localization/products/product-push.md), [arc pair](arc-pair.md)
