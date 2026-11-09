---
article_id: af_befbdb01df3032aa5b6848f6
declaration: theorem
origin: bridged
---

# Coordinates detect $\mathbb L_3(\mathcal S)$

Assume $U(\mathcal S)$. Then $(\pi_{i*})_i:\mathbb L_3(\mathcal S)\to\prod_i\mathbb L_3(\mathrm{Free}\,\mathbb Q[G_i])$ is injective.

*Proof sketch.* Take $x$ with all $\pi_{i*}x=0$. Write $x=\mathrm{cls}\,y$ ([finite-support comparison](finite-support-comparison.md)). Naturality of cls ([induced map on ultimate L](../ultimate/groups/induced-map.md)) gives $\mathrm{cls}\,\pi_{i*}y=0$, so $\pi_{i*}y=0$ ([group-ring comparison](free-comparison.md)). Then $y=0$ by [Finite-support sum](../base/groups/finite-support-sum.md).

## Sources

- HS paper, Section 3 (statement)

## Depends on

- [Ultimate L-group](../ultimate/groups/ultimate-l-group.md)
- [Lemma U](lemma-u.md)

## Proof depends on

- [Point comparison for the finite-support category](finite-support-comparison.md)
- [Point comparison for a group ring](free-comparison.md)
- [Induced map on ultimate L](../ultimate/groups/induced-map.md)
- [Finite-support sum](../base/groups/finite-support-sum.md)
