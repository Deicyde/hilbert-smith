---
article_id: af_e5c3a87de36016919cb83766
declaration: lemma
origin: bridged
---
# Pinch labels

With labels $\kappa(x_b)$, there is $\eta_i\to0$ such that:
1. every cell of $D_i$ not in $Q^{(1)}_i$ has its label in $A_1$;
2. cells of $Q^{(m)}_i$ have labels within $\eta_i$ of $B_m$, and cells of $\partial Q^{(m)}_i$ within $\eta_i$ of $Y_m$;
3. cells of $\partial Q^{(m-1)}_i$ not in $Q^{(m)}_i$ have labels within $\eta_i$ of $A_m$ ($m\ge2$);
4. the bottom and top vertex of the arc $Q^{(n)}_i$ have labels within $\eta_i$ of $y_-$ and $y_+$.

*Proof sketch.* $K\subseteq|Q^{(1)}_i|\subseteq N_{h_i}(K)$ ([box hull properties](../chain-models/grid/box-hull-properties.md) (2)). (1) A cell outside the box has a centre coordinate outside $(-a,a)$, and $\kappa$ maps such points into $A_1$. (2)-(4) A centre in a face of $|Q^{(m)}_i|$ is within $h_i$ of the matching face of $K$, which $\kappa$ maps onto the matching face of $[-s,s]^n$. Take $\eta_i=\omega_\kappa(h_i)$.

## Sources
- New.
## Depends on
- [Pinch faces](pinch-faces.md), [cut sets](cut-sets.md)
## Proof depends on
- [Box hull properties](../chain-models/grid/box-hull-properties.md)
