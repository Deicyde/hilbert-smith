---
article_id: af_4465e6c5742b3f9932201a38
declaration: def
origin: bridged
statement: formalized
lean: HSP.Evaluation.scalarComponentProj
---

# Scalar component projection

Let $n\ge1$ and $s>0$, and let $Y_n=\{y_-,y_+\}$ be the last of the [cut sets](../corner/cut-sets.md) for $n$ and $s$, with $y_-\ne y_+$ ([cut flag](../corner/cut-flag.md)). Work in $\mathcal A_{\mathbf 1}(S^n)$ for the trivial group sequence $\mathbf 1$, with $S^n$ the [round sphere](../corner/round-sphere.md). The *scalar component projection* $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$ is the composite of the following maps on ultimate L:
1. $q_*$, for the [quotient functor](../l-theory/base/categories/filtration-quotient.md) $q:\mathcal A_{Y_n}\to\mathcal A_{Y_n}/\mathcal A_{\{y_-\}}$ of the [support filtration](../categories/supports/support-filtration.md) of $\{y_-\}\subseteq Y_n$;
2. $(e_*)^{-1}$, for the [excision equivalence](../categories/supports/excision.md) $e:\mathcal A_{\{y_+\}}/\mathcal A_\varnothing\to\mathcal A_{Y_n}/\mathcal A_{\{y_-\}}$ of $A=\{y_+\}$, $B=\{y_-\}$, where the quotient realized by the excision is identified with $\mathcal A_{\{y_+\}}/\mathcal A_\varnothing$ by the [quotient of an excisive intersection](excisive-intersection-quotient.md);
3. $(q'_*)^{-1}$, for the [quotient isomorphism by the empty support](../categories/supports/quotient-by-empty.md) $q':\mathcal A_{\{y_+\}}\to\mathcal A_{\{y_+\}}/\mathcal A_\varnothing$;
4. $(P_*)^{-1}$, for the inclusion $P:\mathcal A_{\mathbf 1}(\{y_+\})\to\mathcal A_{\{y_+\}}$ of the [relabelling equivalence](../categories/functors/relabelling-equivalence.md) for $S=\{y_+\}$;
5. $\Phi_*$, for [forgetting labels](../categories/functors/forget-labels.md) $\Phi:\mathcal A_{\mathbf 1}(\{y_+\})\to\mathcal V_{\mathbf 1}$.

The inverses exist. $\{y_\pm\}$ are closed and invariant (the group acts trivially on $S^n$), $\{y_+\}\cap\{y_-\}=\varnothing$ and $\{y_+\}\cup\{y_-\}=Y_n$, so $e$ is a duality equivalence with unitary unit and counit; $q'$ is an isomorphism of duality categories; and $P$ has the strict inverse equivalence $R$ with $RP=\mathrm{id}$ and a unitary counit. In each case [equivalence invariance](../l-theory/ultimate/groups/equivalence-invariance.md) makes the induced map an isomorphism. All maps are [induced maps](../l-theory/ultimate/groups/induced-map.md).

**Remark (not formalized).** No prime, group sequence or control space enters. The version over a control space $T$ is the [component projection](component-projection.md); the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) ends in this one.

## Sources

- HS paper, Section 12 (the projection to one component).

## Depends on

- [The cut sets](../corner/cut-sets.md)
- [Cut flag](../corner/cut-flag.md)
- [The round sphere](../corner/round-sphere.md)
- [Quotient by a filtration](../l-theory/base/categories/filtration-quotient.md)
- [Support filtration](../categories/supports/support-filtration.md)
- [Excision equivalence](../categories/supports/excision.md)
- [Quotient of an excisive intersection](excisive-intersection-quotient.md)
- [Quotient by the empty support](../categories/supports/quotient-by-empty.md)
- [Relabelling equivalence](../categories/functors/relabelling-equivalence.md)
- [Forgetting labels](../categories/functors/forget-labels.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
