---
article_id: af_25df0020e6965002239bec6f
declaration: lemma
origin: bridged
---

# Naturality of the cut boundary

Let $(A,B,Z)$ in $X$ and $(A',B',Z')$ in $X'$ be data as in the [cut boundary](cut-boundary.md), with $S=A\cup B$, $Y=A\cap B$, $S'=A'\cup B'$ and $Y'=A'\cap B'$. Let $F:\mathcal A_{\mathbf G}(X)\to\mathcal A_{\mathbf G'}(X')$ be a strict duality functor carrying $\mathcal A_S,\mathcal A_A,\mathcal A_B,\mathcal A_Z$ into $\mathcal A_{S'},\mathcal A_{A'},\mathcal A_{B'},\mathcal A_{Z'}$. Then $F(\mathcal A_Y)\subset\mathcal A_{Y'}$, and
$$\partial_{A',B'}\circ\bar F_*=(F|_{\mathcal A_Y})_*\circ\partial_{A,B}:\mathbb L_k(\mathcal A_S/\mathcal A_Z)\to\mathbb L_{k-1}(\mathcal A_{Y'}),$$
where $\bar F:\mathcal A_S/\mathcal A_Z\to\mathcal A_{S'}/\mathcal A_{Z'}$ is $M\mapsto F(M)$, $[u]\mapsto[F(u)]$.

*Proof sketch.*
1. [Support intersection](../supports/support-intersection.md) gives $F(\mathcal A_Y)\subset\mathcal A_{Y'}$.
2. $F$ carries maps that factor through $\mathcal A_Z$ to maps that factor through $\mathcal A_{Z'}$, so $\bar F$ is a well-defined strict duality functor, and it carries $\mathcal U_A,\mathcal U_B$ into $\mathcal U_{A'},\mathcal U_{B'}$. [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md) for the two cut squares gives $\partial^{\rm exc}_{A',B'}\circ\bar F_*=(\bar F|_{\mathcal U_Y})_*\circ\partial^{\rm exc}_{A,B}$.
3. Let $s:\mathcal A_Y\to\mathcal U_Y$ and $s':\mathcal A_{Y'}\to\mathcal U_{Y'}$ be the separated-support functors, with inverses $\sigma,\sigma'$. Then $\bar F|_{\mathcal U_Y}\circ s=s'\circ F|_{\mathcal A_Y}$ strictly, both being $M\mapsto F(M)$, $[u]\mapsto[F(u)]$. Hence $\sigma'\circ\bar F|_{\mathcal U_Y}=F|_{\mathcal A_Y}\circ\sigma$, and [functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) finishes the proof.

**Remark (not formalized).** The hypotheses hold for a [pushforward](../functors/pushforward.md) $f_*$ whenever $f(S)\subset S'$, $f(A)\subset A'$, $f(B)\subset B'$ and $f(Z)\subset Z'$, by [pushforward preserves support](../functors/push-support.md); for [forgetting the group](../functors/forget-group.md) with the same sets, by [forgetting the group preserves support](../functors/forget-group-support.md); and for [forgetting the control space](../functors/forget-control.md) from cut data $(T\times A,T\times B,T\times Z)$ in $T\times X$ to $(A,B,Z)$ in $X$, by [forgetting the control space preserves support](../functors/forget-control-support.md). Composites of such functors also qualify.

## Sources

- HS paper, Section 6

## Depends on

- [Cut boundary](cut-boundary.md)

## Proof depends on

- [Support intersection](../supports/support-intersection.md)
- [Naturality of the excision boundary](../../l-theory/ultimate/boundary/excision-boundary-naturality.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
