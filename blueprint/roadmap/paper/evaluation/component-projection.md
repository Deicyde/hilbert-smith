---
article_id: af_7de148f6d466ace8c5456f6e
declaration: def
origin: bridged
---
# Component projection

Let $Y_n=\{y_-,y_+\}$ be the last cut set of the [standing data](../corner/standing-data.md) ([cut flag](../corner/cut-flag.md)). Over $T\times S^n$, with $T$ and $\mathbf G$ from the standing data, $\pi_+:\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ is the composite of the following maps:
- the quotient by $\mathcal A_{T\times y_-}$;
- the inverse of the [excision](../categories/supports/excision.md) $\mathcal A_{T\times y_+}/\mathcal A_\varnothing\to\mathcal A_{T\times Y_n}/\mathcal A_{T\times y_-}$;
- the inverse of the quotient isomorphism by $\mathcal A_\varnothing$;
- the inverse of the [relabelling equivalence](../categories/functors/relabelling-equivalence.md);
- [pushforward](../categories/functors/pushforward.md) along $T\times\{y_+\}\cong T$.

Without $T$ (only $n$ and $s$ enter), the same steps reach $\mathbb L_4(\mathcal A_{\mathbf 1}(\{y_+\}))$, and then [forgetting labels](../categories/functors/forget-labels.md) $\Phi$ gives $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$.

## Sources
- HS paper, Section 12 (the projection to one component).
## Depends on
- [Standing data](../corner/standing-data.md), [cut flag](../corner/cut-flag.md), [excision](../categories/supports/excision.md), [relabelling equivalence](../categories/functors/relabelling-equivalence.md), [pushforward](../categories/functors/pushforward.md), [forgetting labels](../categories/functors/forget-labels.md), [support filtration](../categories/supports/support-filtration.md), [induced map on ultimate L](../l-theory/ultimate/groups/induced-map.md)
