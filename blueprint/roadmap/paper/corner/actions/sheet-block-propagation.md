---
article_id: af_62861c927249eb9b59c87259
declaration: lemma
origin: bridged
---

# Sheet blocks after forgetting

Let $U_{\rm c}$ be [forgetting the control space](../../categories/functors/forget-control.md) for $X=S^n$, so at level $i$, $U_{\rm c}\operatorname{Ind}M=\bigoplus_{s\in G_i}M$ with sheet $s$ labeled by the sphere labels $z_b$. Let $j_s$ and $\pi_s$ be the inclusion and projection of sheet $s$. A matrix $w:U_{\rm c}\operatorname{Ind}M\to U_{\rm c}\operatorname{Ind}M'$ with blocks $w_{s's}=\pi_{s'}wj_s$ satisfies
$$\operatorname{prop}(w)\le\max_{s',s}\operatorname{prop}(w_{s's}).$$

*Proof sketch.* Each sheet carries the labels $z_b$, so $j_s,\pi_s$ preserve labels and have propagation $0$. Write $w=\sum_{s',s}j_{s'}w_{s's}\pi_s$ and apply the bounds for [products](../../categories/asymptotic/prop-mul.md) and [sums](../../categories/asymptotic/prop-add.md).

## Sources

- New: the count-free bound for the scalar image.

## Depends on

- [Induction](induction.md)
- [Forgetting the control space](../../categories/functors/forget-control.md)

## Proof depends on

- [Propagation of a product](../../categories/asymptotic/prop-mul.md)
- [Propagation of a sum](../../categories/asymptotic/prop-add.md)
