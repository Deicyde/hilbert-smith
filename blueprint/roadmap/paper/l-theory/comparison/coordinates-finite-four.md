---
article_id: af_cf08e17b4f0c811e59f2b640
declaration: theorem
origin: bridged
---

# Classes in $\mathbb L_4(\mathcal S)$ have finite support

Let $\mathbf G=(G_i,\chi_i)$ be a [group sequence](../../categories/asymptotic/group-sequence.md), $\mathcal S_{\mathbf G}$ its [finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md), and $\pi_i:\mathcal S_{\mathbf G}\to\mathrm{Free}(G_i)$ the coordinate functors to the [free categories](../../categories/asymptotic/free-category.md). For every $x\in\mathbb L_4(\mathcal S_{\mathbf G})$, $\pi_{i*}x=0$ for all but finitely many $i$.

*Proof sketch.* Write $x=\mathrm{cls}\,y$ ([finite-support comparison](finite-support-comparison.md)). [Finite-support sum](../base/groups/finite-support-sum.md) gives $\pi_{i*}y=0$ off a finite set. Naturality of cls ([induced map on ultimate L](../ultimate/groups/induced-map.md)) finishes.

## Sources

- HS paper, Section 3 (statement)

## Depends on

- [Ultimate L-group](../ultimate/groups/ultimate-l-group.md)
- [Group sequence](../../categories/asymptotic/group-sequence.md)
- [Finite-support subcategory](../../categories/asymptotic/eventually-zero-subcategory.md)
- [Free category](../../categories/asymptotic/free-category.md)

## Proof depends on

- [Point comparison for the finite-support category](finite-support-comparison.md)
- [Finite-support sum](../base/groups/finite-support-sum.md)
- [Induced map on ultimate L](../ultimate/groups/induced-map.md)
