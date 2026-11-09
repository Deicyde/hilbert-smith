---
declaration: def
origin: bridged
---
# Component projection

Let $Y_n=\{y_-,y_+\}$. Over $T\times S^n$, $\pi_+:\mathbb L_4(\mathcal A_{T\times Y_n})\to\mathbb L_4(\mathcal A_{\mathbf G}(T))$ is the composite of the following maps:
- the quotient by $\mathcal A_{T\times y_-}$;
- the inverse of the [excision](../categories/excision.md) $\mathcal A_{T\times y_+}/\mathcal A_\varnothing\to\mathcal A_{T\times Y_n}/\mathcal A_{T\times y_-}$;
- the inverse of the quotient isomorphism by $\mathcal A_\varnothing$;
- the inverse of the [relabelling equivalence](../categories/relabelling-equivalence.md);
- [pushforward](../categories/pushforward.md) along $T\times\{y_+\}\cong T$.

Without $T$, the same steps reach $\mathbb L_4(\mathcal A_{\mathbf 1}(\{y_+\}))$, and then [forgetting labels](../categories/forget-labels.md) $\Phi$ gives $\pi_+:\mathbb L_4(\mathcal A_{Y_n})\to\mathbb L_4(\mathcal V_{\mathbf 1})$.

## Sources
- HS paper, Section 12 ("project onto one component").
## Depends on
- [Cut sets](cut-sets.md), [excision](../categories/excision.md), [relabelling equivalence](../categories/relabelling-equivalence.md), [D2](../l-theory/D2.md)
