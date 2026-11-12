---
article_id: af_305ef480e6f59a68af10da7d
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.Compression.endpoint
---
# Endpoint lemma

Let $i\ge i_0$, let $M_0,M_1,M_2$, $p_j$, $\jmath_j$ and $Q_1$ be as in the [product rule](compression-product-rule.md), and let $\alpha:M_1\to M_2$ and $\beta:M_0\to M_1$ lie in $\mathcal P_i$ ([chain-model estimates](../chain-models/grid/chain-model-estimates.md)), with types $c_\alpha,c_\beta\in C_p$. Let $W$ be the span in $M_1$ of the discarded cells (or their duals) that lie in $\mathcal B_i(u)$ ([buffered cells](../chain-models/grid/buffers/buffered-cells.md)), with the [control labels](../chain-models/grid/buffers/control-labels.md), and let $\iota_W,p_W$ be its inclusion and projection. Then:
1. $p_2\,\alpha\,Q_1\,\beta\,\jmath_0=x\,y$, with $y=p_W\beta\jmath_0$ and $x=p_2\alpha\iota_W$;
2. $y$ has [graph type](../corner/actions/graph-type.md) $c_\beta$ and $x$ has graph type $c_\alpha$, both with bound $\delta_i$, the [bound sequence](bound-sequence.md);
3. every label of $W$ lies in $Z=T\times Z_0$, for the [exterior](../corner/exterior.md) $Z_0$ of $n$ and the buffer radius $R$.

Hence $p_2\alpha Q_1\beta\jmath_0$ is an [exterior witness](../corner/actions/exterior-witness.md) of type $c_\alpha+c_\beta$ with bound $\delta_i$.

*Proof sketch.*
1. Retained cells lie in $\mathcal B_i(t')$ ([buffers](buffer-eventually.md) (1)), so $\beta\jmath_0=\iota_u\,p_u\beta\jmath_0$ by buffers (2): a nonzero entry of $\beta$ from a retained cell lands in $\mathcal B_i(u)$. On $\mathcal B_i(u)$, $Q_1$ is the projection onto $W$, so $Q_1\beta\jmath_0=\iota_Wp_W\beta\jmath_0$.
2. Retained cells and $W$ lie in $\mathcal B_i(u)$, so $y$ and $x$ are submatrices of $\beta^{[u]}$ and $\alpha^{[u]}$; apply buffers (3) and $\delta_i=\epsilon'_i$ for $i\ge i_0$ ([bound sequence](bound-sequence.md)).
3. A cell $w$ of $W$ is discarded, so $f_T$ of its cube misses $\overline B(0,t)$; its sphere label $s_w$, the value of $f_T$ at the centre, has $|s_w|>t>R$ or $s_w=\infty$. So $s_w\in Z_0$, and $\lambda(w)$ has second coordinate $s_w$.
For the witness: $Z$ is $C_p$-invariant and $C_p$ acts isometrically ([graph-type calculus](../corner/actions/graph-type-calculus.md)), so with the labels $\lambda'$ the labels of $W$ stay in $Z$, $y$ has type $0$ and $x$ has type $c_\alpha+c_\beta$, both with bound $\delta_i$.

## Sources
- HS paper, Section 10 (exterior band). New: words of length two suffice, so there is no length parameter and no band.

## Depends on

- [Torus labels of chain-model cells](../chain-models/grid/model/chain-model-label.md)
- [Product rule](compression-product-rule.md)
- [Chain-model estimates](../chain-models/grid/chain-model-estimates.md)
- [Buffered cells](../chain-models/grid/buffers/buffered-cells.md)
- [Control labels](../chain-models/grid/buffers/control-labels.md)
- [Graph-type matrices](../corner/actions/graph-type.md)
- [Exterior witnesses](../corner/actions/exterior-witness.md)
- [Exterior](../corner/exterior.md)
- [Start index](start-index.md)
- [Bound sequence](bound-sequence.md)
- [Retained projection](retained-projection.md)
- [Compressed complex](compressed-complex.md)

## Proof depends on

- [Buffers hold eventually](buffer-eventually.md)
- [Graph-type calculus](../corner/actions/graph-type-calculus.md)
- [Sphere labels](../chain-models/grid/sphere-labels.md)
- [Retained cells](retained-cells.md)
