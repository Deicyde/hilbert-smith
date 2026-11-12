---
article_id: af_1f391d3fa8b54f582438a27b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.forget_supp
---

# Forgetting the group preserves support

Suppose the $C_p$-action on $X$ is isometric. For closed invariant $S\subset X$, [forgetting the group](forget-group.md) carries $\mathcal A_S$ into $\mathcal A_S\subset\mathcal A_{\mathbf 1}(X)$.

The statement needs neither that $S$ is closed nor that $X$ is compact.

*Proof sketch.* The new labels are $\chi_i(g)x_i(k)$, and they are as far from the invariant set $S$ as $x_i(k)$ is.

## Sources

- HS paper, Section 2

## Depends on

- [Forgetting the group](forget-group.md)
- [Support subcategory](../supports/support-subcategory.md)

## Proof depends on

- [The group enumeration](group-enumeration.md)
