---
article_id: af_e5c3a87de36016919cb83766
declaration: lemma
origin: bridged
---
# Pinch labels

Let $n\ge1$ and $s>0$. Take the [cut sets](../corner/cut-sets.md) $A_m,B_m,Y_m$ and $y_\pm$ for $n$ and $s$, in the [round sphere](../corner/round-sphere.md), the [cubical pinch](cubical-pinch.md) $\kappa$ for the same $n$ and $s$, and the [pinch faces](pinch-faces.md) $Q^{(m)}_i$, with each cell $b$ labelled $\kappa(x_b)$. There is $\eta_i\to0$ such that, for $1\le m\le n$:
1. every cell of $D_i$ not in $Q^{(1)}_i$ has its label in $A_1$;
2. cells of $Q^{(m)}_i$ have labels within $\eta_i$ of $B_m$, and cells of $\partial Q^{(m)}_i$ within $\eta_i$ of $Y_m$;
3. for $m\ge2$, cells of $\partial Q^{(m-1)}_i$ not in $Q^{(m)}_i$ have labels within $\eta_i$ of $A_m$;
4. the cells of $\partial Q^{(n)}_i$ at the bottom vertex of its arc have labels within $\eta_i$ of $y_-$, and those at the top vertex within $\eta_i$ of $y_+$.

*Proof sketch.* $K\subseteq|Q^{(1)}_i|\subseteq N_{h_i}(K)$ ([box hull properties](../chain-models/grid/box-hull-properties.md) (2)). (1) A cell outside the box has a centre coordinate outside $(-a,a)$, and $\kappa$ maps such points into $\{|z|_\infty\ge s\}\cup\{\infty\}=A_1$ ([the cubical pinch on the cube](cubical-pinch-faces.md), item 2). (2)-(4) A centre in a face of $|Q^{(m)}_i|$ is within $h_i$ of the matching face of $K$, which $\kappa$ maps onto the matching face of $[-s,s]^n$ (item 1), and the faces of $[-s,s]^n$ that make up $B_m$, $Y_m$, $A_m$ and $y_\pm$ are those of the [cut flag](../corner/cut-flag.md). Take $\eta_i=\omega_\kappa(h_i)$, with $\omega_\kappa$ a modulus of uniform continuity of $\kappa$ for $d_\infty$ and the round metric.

## Sources
- New.
## Depends on
- [Pinch faces](pinch-faces.md)
- [Cubical pinch](cubical-pinch.md)
- [The cut sets](../corner/cut-sets.md)
- [The round sphere](../corner/round-sphere.md)
## Proof depends on
- [Box hull properties](../chain-models/grid/box-hull-properties.md)
- [The cubical pinch on the cube and outside it](cubical-pinch-faces.md)
- [Cut flag](../corner/cut-flag.md)
