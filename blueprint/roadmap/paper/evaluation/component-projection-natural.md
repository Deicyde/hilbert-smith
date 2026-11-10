---
article_id: af_c8af9431decb1b25230dc220
declaration: lemma
origin: bridged
---

# The component projection commutes with forgetting

Take [standing data](../corner/standing-data.md); $Y_n$, $T$ and $\mathbf G$ are theirs, and the scalar $\pi_+$ is the one for their $n$ and $s$. Let $U_{\rm c}$ be [forgetting the control space](../categories/functors/forget-control.md) for $X=S^n$, and let $U_T=\bar U\circ\Phi:\mathcal A_{\mathbf G}(T)\to\mathcal V_{\mathbf G}\to\mathcal V_{\mathbf 1}$, with $\Phi$ [forgetting labels](../categories/functors/forget-labels.md) and $\bar U$ the [forgetful functor on tails](../signatures/point-functors/tail-forget-functor.md). Then $U_{\rm c}$ carries $\mathcal A_{T\times Y_n}$ into $\mathcal A_{Y_n}$, and
$$\pi_+\circ(U_{\rm c}|_{\mathcal A_{T\times Y_n}})_*=U_{T*}\circ\pi_+$$
as maps $\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$, where the left $\pi_+$ is the [scalar component projection](scalar-component-projection.md) and the right one is the [component projection](component-projection.md) over $T$.

*Proof sketch.* (1) $U_{\rm c}$ carries $\mathcal A_{T\times S}$ into $\mathcal A_S$ for every closed invariant $S\subseteq S^n$ ([support](../categories/functors/forget-control-support.md)), so it induces functors on the quotients of the five steps of the component projection; it commutes strictly with the quotient functors and with the excision functors, which are the identity on matrices. (2) It commutes strictly with the inclusions $P$ of the relabelling equivalences for $T\times\{y_+\}$ and $\{y_+\}$ and with the pushforward along $T\times\{y_+\}\cong T$, since all of these keep the matrices and move only labels. (3) At the end, on $\mathcal A_{\mathbf G}(T\times\{y_+\})$, $\Phi\circ U_{\rm c}=U_T\circ\mathrm{pr}_{T*}$ as functors to $\mathcal V_{\mathbf 1}$, where $\mathrm{pr}_T:T\times\{y_+\}\to T$ is the projection and $U_{\rm c}$ lands in $\mathcal A_{\mathbf 1}(\{y_+\})$: both send $(n_i,x_i)$ to $(|G_i|n_i)$, with $G_i\times\{1..n_i\}$ enumerated in the fixed order of [forgetting the group](../categories/functors/forget-group.md), and $[u]$ to the class of the same matrices. (4) Equal composites of functors induce equal maps on $\mathbb L_4$ ([functoriality](../l-theory/ultimate/groups/induced-map-comp.md)). The inverses in the two projections are inverses of induced isomorphisms ([equivalence invariance](../l-theory/ultimate/groups/equivalence-invariance.md)), among them the inverses of the [quotient isomorphisms by the empty support](../categories/supports/quotient-by-empty.md); if $F_*a=a'_*F'_*$ with $a_*,a'_*$ invertible, then $a'^{-1}_*F_*=F'_*a_*^{-1}$, so by (1)-(2) the inverses commute with the induced functors.

## Sources

- HS paper, Section 12 (the projection to one component).

## Depends on

- [Standing data](../corner/standing-data.md)
- [Scalar component projection](scalar-component-projection.md)
- [Component projection](component-projection.md)
- [Forgetting the control space](../categories/functors/forget-control.md)
- [Forgetting labels](../categories/functors/forget-labels.md)
- [The forgetful functor on tails](../signatures/point-functors/tail-forget-functor.md)

## Proof depends on

- [Forgetting the control space preserves supports](../categories/functors/forget-control-support.md)
- [Forgetting the group](../categories/functors/forget-group.md)
- [Functoriality on ultimate L](../l-theory/ultimate/groups/induced-map-comp.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Quotient by the empty support](../categories/supports/quotient-by-empty.md)
