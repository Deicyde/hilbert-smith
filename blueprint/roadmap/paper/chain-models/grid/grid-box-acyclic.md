---
article_id: af_bec2a6ea0ad99585d41b2635
declaration: lemma
origin: background
statement: formalized
lean: HSP.ChainModels.box_acyclic
---
# Boxes are acyclic

Every grid box $B$, as the subcomplex of the grid complex given in each degree by the [span](cube-span.md) of its cubes, is augmented acyclic: $H_r(B)=0$ for $r>0$, and $\varepsilon$ induces $H_0(B)\cong\mathbb Q$.

*Proof sketch.* On an arc starting at $[w]$, put $s[w+j]=e_w+\dots+e_{w+j-1}$ and $s(e)=0$. Then $ds+sd=1-[w]\varepsilon$. Tensor these contractions over the $n$ factors [U].

## Sources
- [published: Künneth over a field] [U]. New: the arc contraction.
## Depends on

- [Spans of cubes](cube-span.md)
- [Cubical torus grid](cubical/cubical-torus-grid.md)
- [Augmentation of the grid complex](cubical/grid-aug.md)
- [Grid boxes](grid-box.md)
- [The category of based ℚ-vector spaces](../../l-theory/localization/products/bookkeeping/based-category.md)

## Proof depends on

- [Grid cubes](cubical/grid-cube.md)
- [The cube of a basis vector](cubical/grid-cell.md)
