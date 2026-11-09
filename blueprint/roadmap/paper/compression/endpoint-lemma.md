---
article_id: af_305ef480e6f59a68af10da7d
declaration: lemma
origin: bridged
---
# Endpoint lemma

Let $i\ge i_0$, and let $u:M_1\to M_2$ and $v:M_0\to M_1$ lie in $\mathcal P_i$, with types $c_u,c_v$ and notation as in the [product rule](compression-product-rule.md). Let $W$ be the span in $M_1$ of the discarded cells (or their duals) lying in $\mathcal B_i(u)$, with inclusion $\iota_W$ and projection $p_W$. Then:
1. $p_2uQ_1v\jmath_0=x\,y$, with $y=p_Wv\jmath_0$ and $x=p_2u\iota_W$;
2. $y$ has graph type $c_v$ and $x$ graph type $c_u$, with bound $\delta_i$;
3. every label of $W$ lies in $Z=T\times Z_0$.

Hence $p_2uQ_1v\jmath_0$ is an [exterior witness](../corner/actions/graph-type.md) of type $c_u+c_v$ with bound $\delta_i$.

*Proof sketch.* Take a nonzero term $u_{b'w}v_{wb}$ with $b,b'$ retained and $w$ discarded. Then $b\in\mathcal B_i(t')$, and the sphere propagation of $v$ is less than $\gamma$, so $s_w\in B(0,u)$ and $w\in W$. This gives (1). The entries of $x$ and $y$ join cells of $\mathcal B_i(u)$, which gives (2) by [buffers](buffer-eventually.md) (3). For (3): $w$ is discarded, so $x_w\notin K_t$ and $|s_w|>t>R$, or $s_w=\infty$; thus $s_w\in Z_0$. Also $\tilde x_w\in U^+\subseteq Z^+$, so $\pi(\tilde x_w)$ is defined. Relabel $W$ by $-c_v$, using that $Z$ is $C_p$-invariant and $C_p$ acts isometrically: $y$ becomes type $0$ and $x$ type $c_u+c_v$.

## Sources
- HS paper, Section 10 (exterior band). New: words of length two suffice, so there is no length parameter and no band.
## Depends on
- [Buffers](buffer-eventually.md), [graph-type matrices](../corner/actions/graph-type.md), [product rule](compression-product-rule.md)
## Proof depends on
- [Buffered restriction](../chain-models/approximations/buffered-restriction.md), [control action isometric](../local-data/control/control-action-isometric.md)
