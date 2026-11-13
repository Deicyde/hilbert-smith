---
article_id: af_4465e6c5742b3f9932201a38
declaration: def
origin: bridged
statement: formalized
lean: HSP.Evaluation.scalarComponentProj
---

# Scalar component projection

Let $p$ be a natural number, $n\ge1$ and $s>0$, and let $Y_n=\{y_-,y_+\}$ be the last of the [cut sets](../corner/cut-sets.md) for $n$ and $s$, with $y_-\ne y_+$ ([cut flag](../corner/cut-flag.md)). Work in $\mathcal A_{\mathbf 1}(S^n)$ for the [trivial group sequence](../categories/asymptotic/trivial-group-sequence.md) $\mathbf 1$ with values in $\mathbb Z/p$, with $S^n$ the [round sphere](../corner/round-sphere.md), on which $\mathbb Z/p$ acts trivially. Inside $\mathcal A_{Y_n}$ let $\mathcal U_+$ and $\mathcal U_-$ be the [subcategories](../categories/supports/relative-support.md) of $\{y_+\}$- and $\{y_-\}$-supported objects. The *scalar component projection* $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$ is the composite of the following maps on ultimate L:
1. $q_*$, for the [quotient functor](../l-theory/base/categories/filtration-quotient.md) $q:\mathcal A_{Y_n}\to\mathcal A_{Y_n}/\mathcal A_{\{y_-\}}$ of the [support filtration](../categories/supports/support-filtration.md) of $\{y_-\}\subseteq Y_n$;
2. $(e_*)^{-1}$, for the [excision equivalence](../categories/supports/excision.md) $e:\mathcal U_+/(\mathcal U_+\cap\mathcal U_-)\to\mathcal A_{Y_n}/\mathcal A_{\{y_-\}}$ of $A=\{y_+\}$, $B=\{y_-\}$ and $S=Y_n$, followed by the map induced by the identification $\mathcal U_+/(\mathcal U_+\cap\mathcal U_-)\to\mathcal A_{\{y_+\}}/\mathcal A_\varnothing$ of the [quotient of an excisive intersection](excisive-intersection-quotient.md) for $A=\{y_+\}$, $B=\{y_-\}$, $S=Y_n$ and $C=\varnothing$;
3. $(q'_*)^{-1}$, for the [quotient isomorphism by the empty support](../categories/supports/quotient-by-empty.md) $q':\mathcal A_{\{y_+\}}\to\mathcal A_{\{y_+\}}/\mathcal A_\varnothing$;
4. $(P_*)^{-1}$, for the inclusion $P:\mathcal A_{\mathbf 1}(\{y_+\})\to\mathcal A_{\{y_+\}}$ of the [relabelling equivalence](../categories/functors/relabelling-equivalence.md) for $S=\{y_+\}$;
5. $\Phi_*$, for [forgetting labels](../categories/functors/forget-labels.md) $\Phi:\mathcal A_{\mathbf 1}(\{y_+\})\to\mathcal V_{\mathbf 1}$.

The maps are defined. $\{y_\pm\}$ are closed and invariant (the group acts trivially on $S^n$), $\{y_+\}$ is compact, $\{y_+\}\cap\{y_-\}=\varnothing$ and $\{y_+\}\cup\{y_-\}=Y_n$, so $e$ is a duality equivalence with unitary unit and counit, and the identification of step 2 is a strict duality functor; $q'$ is an isomorphism of duality categories; and $P$ has the strict inverse equivalence $R$ with $RP=\mathrm{id}$ and a unitary counit. In each case [equivalence invariance](../l-theory/ultimate/groups/equivalence-invariance.md) makes the induced map an isomorphism, so the inverses exist. All maps are [induced maps](../l-theory/ultimate/groups/induced-map.md).

**Remark (not formalized).** The number $p$ enters only through the trivial group sequence and need not be prime; no other group sequence and no control space enters. The version over a control space $T$ is the [component projection](component-projection.md); the [scalar iterated cut](../corner/theorem/scalar-iterated-cut.md) ends in this one.

## Sources

- HS paper, Section 12 (the projection to one component).

## Depends on

- [Ultimate L-group](../l-theory/ultimate/groups/ultimate-l-group.md)
- [Support subcategory](../categories/supports/support-subcategory.md)
- [The trivial group sequence](../categories/asymptotic/trivial-group-sequence.md)
- [The boundary of the cube face](../corner/cut-face-boundary.md)
- [Point category](../categories/asymptotic/point-quotient.md)
- [Asymptotic category](../categories/asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../categories/asymptotic/asymptotic-duality.md)
- [Finite-support subcategory](../categories/asymptotic/eventually-zero-subcategory.md)
- [Point filtration](../categories/asymptotic/point-filtration.md)
- [Sequence category](../categories/asymptotic/point-sequence-category.md)
- [The asymptotic category has finite biproducts](../categories/asymptotic/structure/biproducts.md)
- [The support subcategory is additive](../categories/supports/support-dual-additive.md)
- [The round sphere](../corner/round-sphere.md)
- [Duality category of a dual-closed subcategory](../l-theory/base/categories/dual-subcategory.md)
- [Quotient by a subcategory](../l-theory/base/categories/filtration-quotient.md)

## Proof depends on

- [Cut flag](../corner/cut-flag.md)
- [The point y₊](../corner/cut-point-plus.md)
- [The point y₋](../corner/cut-point-minus.md)
- [The quotient duality functor](../l-theory/base/categories/quotient-duality-functor.md)
- [Excisive pair of filtrations](../l-theory/ultimate/boundary/excisive-pair.md)
- [Excision equivalence](../categories/supports/excision.md)
- [Quotient of an excisive intersection](excisive-intersection-quotient.md)
- [Quotient by the empty support](../categories/supports/quotient-by-empty.md)
- [Relabelling equivalence](../categories/functors/relabelling-equivalence.md)
- [Forgetting labels](../categories/functors/forget-labels.md)
- [Duality functor](../l-theory/base/categories/duality-functor.md)
- [Unitary natural isomorphism](../l-theory/base/categories/unitary-isomorphism.md)
- [Small Q-linear category with strict duality](../l-theory/base/categories/duality-category.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
- [Supported objects of a relative support subcategory are additive](../categories/supports/relative-intersection-additive.md)
- [The support subcategory inside a support subcategory is additive](../categories/supports/relative-support-additive.md)
- [Support subcategory inside a support subcategory](../categories/supports/relative-support.md)
- [The cube face](../corner/cut-face.md)
- [The cut sets](../corner/cut-sets.md)
- [Additive subcategory closed under duality](../l-theory/base/categories/dual-additive-subcategory.md)
- [Identity and composite duality functors](../l-theory/base/categories/duality-functors/composite-duality-functor.md)
- [Strict duality functor](../l-theory/base/categories/duality-functors/strict-duality-functor.md)
- [Intersection of full subcategories](../l-theory/ultimate/boundary/excisive-intersection.md)
