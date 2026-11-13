---
article_id: af_79680581d62738197897e328
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.forgetControl_supp
---

# Forgetting the control space preserves support

In the setting of [forgetting the control space](forget-control.md), let $S\subset X$ be closed. Then $U_{\rm c}$ carries $\mathcal A_{T\times S}$ into $\mathcal A_S\subset\mathcal A_{\mathbf 1}(X)$.

The statement needs neither that $S$ is closed nor that the action on $T$ is isometric.

*Proof sketch.* $\mathrm{pr}(T\times S)\subset S$, so [pushforward preserves support](push-support.md) gives $\mathrm{pr}_*(\mathcal A_{T\times S})\subset\mathcal A_S$. The trivial action is isometric and every subset is invariant for it, so [forgetting the group preserves support](forget-group-support.md) gives the rest.

## Sources

- HS paper, Section 12

## Depends on

- [Forgetting the control space](forget-control.md)
- [Support subcategory](../supports/support-subcategory.md)
- [Asymptotic category](../asymptotic/asymptotic-category.md)
- [Duality on the asymptotic category](../asymptotic/asymptotic-duality.md)
- [Group sequence](../asymptotic/group-sequence.md)
- [The asymptotic category has finite biproducts](../asymptotic/structure/biproducts.md)
- [The trivial group sequence](../asymptotic/trivial-group-sequence.md)
- [Duality functor](../../l-theory/base/categories/duality-functor.md)

## Proof depends on

- [Pushforward preserves support](push-support.md)
- [Forgetting the group preserves support](forget-group-support.md)
- [Pushforward of labels](pushforward.md)
