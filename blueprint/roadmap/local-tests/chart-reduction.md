---
article_id: af_888c4032a0cb62dfbd880ef9
declaration: theorem
origin: cited
lean: HilbertSmith.Interface.chartReductionNoSC HilbertSmith.Interface.isClosed_interior_fixSet HilbertSmith.Interface.exists_forall_fixSet_notMem_nhds HilbertSmith.Interface.exists_invariant_chart_subset
---

# Invariant chart subset

There are an open subgroup $G \cong \Zp$ and a nonempty connected
$G$-invariant open subset $O$ of a coordinate chart of $M$ such that
$G$ acts faithfully and preserves orientation on $O$. In particular
$O$ may be regarded as an actual open subset of $\R^n$.

*Proof sketch.* Some point $x$ has no open subgroup fixing a
neighborhood pointwise: otherwise some interior fixed set $F_j$ is
nonempty, and it is closed because near a boundary point the action
factors through a finite group to which Newman rigidity applies,
contradicting faithfulness. Saturating a small ball at $x$ gives a
connected invariant $O$; a nonzero restriction kernel would be an
open subgroup fixing $O$, impossible. Passing to squares preserves
orientation (index two only for $p = 2$).

*Formalization.* `chartReductionNoSC` proves, from Newman rigidity and
without second countability of $M$, the part of this statement that the
contradiction uses: a faithful action of $\Zp$ on a connected open
subset of $\R^n$. The open subgroup and the chart are not recorded, and
the orientation clause is not proved here: it is the input
`Orientation.exists_restrict` of `LocalInputs`.

## Sources

- [Preprint source map: `prop:chart-reduction`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Newman rigidity](../background/newman-rigidity.md)
- [Closed subgroups of $\Zp$](../background/padic-subgroups.md)
