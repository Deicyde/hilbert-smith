---
article_id: af_1d7b256f6b1ec1517182ca42
declaration: theorem
origin: cited
---

# Objects supported in an open set

For an open inclusion $j : U \hookrightarrow X$, the essential image
of $j_! : \Bcat(U) \to \Bcat(X)$ consists exactly of those objects
whose cohomology vanishes outside some compact subset of $U$. This
image is a thick, duality-stable subcategory.

*Proof sketch.* Extended objects have such a support bound. For the
converse, write the object as a summand of $A \in \Bzero(X)$, cut
off over $U$ invertibly near the support, and lift the splitting
through open-extension adjunction; restricting exhibits the object
as extended from $U$. Thickness follows from the cohomology long
exact sequence and stalkwise splitting; duality stability from open
restriction of Verdier duality.

## Sources

- [Preprint source map: `prop:compact-support`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)

## Proof depends on

- [Cutoff](cutoff.md)
- [Verdier duality on test categories](../sheaf-categories/test-duality.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
