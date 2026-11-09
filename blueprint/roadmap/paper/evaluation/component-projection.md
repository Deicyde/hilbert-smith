---
article_id: af_7de148f6d466ace8c5456f6e
declaration: def
origin: bridged
---
# Component projection

Let $Y_n=\{y_-,y_+\}$. Over $T\times S^n$, $\pi_+:\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ is the composite of the following maps:
- the quotient by $\mathcal A_{T\times y_-}$;
- the inverse of the [excision](../categories/supports/excision.md) $\mathcal A_{T\times y_+}/\mathcal A_\varnothing\to\mathcal A_{T\times Y_n}/\mathcal A_{T\times y_-}$;
- the inverse of the quotient isomorphism by $\mathcal A_\varnothing$;
- the inverse of the [relabelling equivalence](../categories/functors/relabelling-equivalence.md);
- [pushforward](../categories/functors/pushforward.md) along $T\times\{y_+\}\cong T$.

Without $T$, the same steps reach $\mathbb L_4(\mathcal A_{\mathbf 1}(\{y_+\}))$, and then [forgetting labels](../categories/functors/forget-labels.md) $\Phi$ gives $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$.

## Sources
- HS paper, Section 12 ("project onto one component").
## Depends on
- [Cut sets](cut-sets.md), [excision](../categories/supports/excision.md), [relabelling equivalence](../categories/functors/relabelling-equivalence.md), [induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
