---
article_id: af_7de148f6d466ace8c5456f6e
declaration: def
origin: bridged
---
# Component projection

Let $Y_n=\{y_-,y_+\}$ be the last cut set of the [standing data](../corner/standing-data.md) ([cut flag](../corner/cut-flag.md)). Over $T\times S^n$, with $T$ and $\mathbf G$ from the standing data, $\pi_+:\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ is the composite of the following maps:
- the quotient by $\mathcal A_{T\times y_-}$ (the [support filtration](../categories/supports/support-filtration.md) of $T\times\{y_-\}\subseteq T\times Y_n$);
- the inverse of the [excision](../categories/supports/excision.md) $\mathcal U_+/(\mathcal U_+\cap\mathcal U_-)\to\mathcal A_{T\times Y_n}/\mathcal A_{T\times y_-}$ for $A=T\times\{y_+\}$ and $B=T\times\{y_-\}$, where $\mathcal U_\pm$ are the [subcategories](../categories/supports/relative-support.md) of $T\times\{y_\pm\}$-supported objects of $\mathcal A_{T\times Y_n}$, followed by the identification $\mathcal U_+/(\mathcal U_+\cap\mathcal U_-)\to\mathcal A_{T\times y_+}/\mathcal A_\varnothing$ of the [quotient of an excisive intersection](excisive-intersection-quotient.md) ($T\times S^n$ is compact, and $T\times\{y_\pm\}$ are closed and disjoint);
- the inverse of the [quotient isomorphism by the empty support](../categories/supports/quotient-by-empty.md) $\mathcal A_{T\times y_+}\to\mathcal A_{T\times y_+}/\mathcal A_\varnothing$;
- the inverse of the [relabelling equivalence](../categories/functors/relabelling-equivalence.md) for $T\times\{y_+\}$, which is nonempty because $T$ is;
- [pushforward](../categories/functors/pushforward.md) along $T\times\{y_+\}\cong T$.

Each inverse is the inverse of an induced isomorphism on ultimate L, by [equivalence invariance](../l-theory/ultimate/groups/equivalence-invariance.md); all maps are [induced maps](../l-theory/ultimate/groups/induced-map.md).

**Remark (not formalized).** The version without $T$, which needs only $n$ and $s$ and ends in $\mathbb L_4(\mathcal V_{\mathbf 1})$, is the [scalar component projection](scalar-component-projection.md).

## Sources
- HS paper, Section 12 (the projection to one component).
## Depends on
- [Standing data](../corner/standing-data.md)
- [Cut flag](../corner/cut-flag.md)
- [Excision](../categories/supports/excision.md)
- [Support subcategory inside a support subcategory](../categories/supports/relative-support.md)
- [Quotient of an excisive intersection](excisive-intersection-quotient.md)
- [Quotient by the empty support](../categories/supports/quotient-by-empty.md)
- [Relabelling equivalence](../categories/functors/relabelling-equivalence.md)
- [Pushforward](../categories/functors/pushforward.md)
- [Support filtration](../categories/supports/support-filtration.md)
- [Equivalence invariance on ultimate L](../l-theory/ultimate/groups/equivalence-invariance.md)
- [Induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
