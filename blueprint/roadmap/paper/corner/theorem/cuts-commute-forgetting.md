---
article_id: af_08e42a676dcf962f98b8b40e
declaration: lemma
origin: bridged
---

# Cuts commute with forgetting

Take the [standing data](../standing-data.md), the [iterated cut](iterated-cut.md) $\Delta_T$, the [scalar iterated cut](scalar-iterated-cut.md) $\Delta_{\mathbf 1}$ for the same $n$, $R$, $s$, and $U:\mathcal B_{\mathbf G,Z}(T\times S^n)\to\mathcal B_{\mathbf 1,Z_0}(S^n)$, [forgetting to the scalar exterior quotient](scalar-forget.md). Let $U_T=\bar U\circ\Phi:\mathcal A_{\mathbf G}(T)\to\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$ be [forgetting labels](../../categories/functors/forget-labels.md) followed by [the forgetful functor on tails](../../signatures/point-functors/tail-forget-functor.md). Then
$$U_{T*}\circ\Delta_T=\Delta_{\mathbf 1}\circ U_*:\mathbb L_N(\mathcal B_{\mathbf G,Z}(T\times S^n))\to\mathbb L_4(\mathcal V_{\mathbf 1}).$$

This lemma rests on the open statement [Lifting](../../l-theory/localization/boundary/lift-to-pair.md), through the cut boundary.

*Proof sketch.* Let $U_{\rm c}$ be [forgetting the control space](../../categories/functors/forget-control.md) for $X=S^n$.
1. $U_{\rm c}$ carries $\mathcal A_{T\times S}$ into $\mathcal A_S$ for $S=Y_{m-1},A_m,B_m,Z^0_m$ ([forgetting the control space preserves support](../../categories/functors/forget-control-support.md)), and $Z_m=T\times Z^0_m$. So [naturality of the cut boundary](../../categories/cuts/cut-boundary-naturality.md) with $F=U_{\rm c}$ and cut data $(T\times A_m,T\times B_m,Z_m)\to(A_m,B_m,Z^0_m)$ commutes the induced maps past each cut $d_m$.
2. The functors induced by $U_{\rm c}$ commute strictly with $j$ and with each $q$: both composites are $M\mapsto U_{\rm c}M$, $[u]\mapsto[U_{\rm c}u]$. [Functoriality](../../l-theory/ultimate/groups/induced-map-comp.md) commutes the induced maps past $j_*$ and $q_*$.
3. [The component projection commutes with forgetting](../../evaluation/component-projection-natural.md): $\pi_+\circ(U_{\rm c}|_{\mathcal A_{T\times Y_n}})_*=U_{T*}\circ\pi_+$.
4. Compose steps 1 to 3 along the definitions of the two iterated cuts.

## Sources

- HS paper, Section 12.

## Depends on

- [Standing data](../standing-data.md)
- [Iterated cut](iterated-cut.md)
- [Scalar iterated cut](scalar-iterated-cut.md)
- [Forgetting to the scalar exterior quotient](scalar-forget.md)
- [Forgetting labels](../../categories/functors/forget-labels.md)
- [The forgetful functor on tails](../../signatures/point-functors/tail-forget-functor.md)

## Proof depends on

- [Forgetting the control space](../../categories/functors/forget-control.md)
- [Forgetting the control space preserves support](../../categories/functors/forget-control-support.md)
- [Naturality of the cut boundary](../../categories/cuts/cut-boundary-naturality.md)
- [Functoriality on ultimate L](../../l-theory/ultimate/groups/induced-map-comp.md)
- [The component projection commutes with forgetting](../../evaluation/component-projection-natural.md)
