---
article_id: af_62861c927249eb9b59c87259
declaration: lemma
origin: bridged
---

# Sheet blocks after forgetting

Let $U$ forget the group and $T$, so $U\operatorname{Ind}M=\bigoplus_{s\in G_i}M$ with sheet $s$ labeled by the sphere labels $z_b$. The sheet inclusions $j_s$ and projections $\pi_s$ have propagation $0$, and a matrix $w:U\operatorname{Ind}M\to U\operatorname{Ind}M'$ with blocks $w_{s's}=\pi_{s'}wj_s$ satisfies $w=\sum_{s',s}j_{s'}w_{s's}\pi_s$ and
$$\operatorname{prop}(w)\le\max_{s',s}\operatorname{prop}(w_{s's}).$$

*Proof sketch.* Each sheet carries the labels $z_b$, so $j_s,\pi_s$ preserve labels. Then apply the bounds for [products](../../categories/asymptotic/prop-mul.md) and [sums](../../categories/asymptotic/prop-add.md).

## Sources

- New: the count-free bound for the scalar image.

## Depends on

- [Induction](induction.md)
- [Forgetting the group](../../categories/functors/forget-group.md)
- [Pushforward of labels](../../categories/functors/pushforward.md)

## Proof depends on

- [Propagation of a product](../../categories/asymptotic/prop-mul.md)
- [Propagation of a sum](../../categories/asymptotic/prop-add.md)
