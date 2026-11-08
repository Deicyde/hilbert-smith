---
article_id: af_888c4032a0cb62dfbd880ef9
declaration: theorem
origin: cited
lean: HilbertSmith.Interface.chartReductionNoSC HilbertSmith.Interface.isClosed_interior_fixSet HilbertSmith.Interface.exists_forall_fixSet_notMem_nhds HilbertSmith.Interface.exists_invariant_chart_subset HilbertSmith.Interface.LocalAction.exists_orientationPreserving_restrict
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

*Remark.* The argument does not use second countability of $M$.
The orientation step also works without the preserve-or-reverse
dichotomy behind passing to squares. Call $g$ orientation-preserving
if, for every ball $B(x, \varepsilon) \subset O$, its local map
$v \mapsto g(x + \varepsilon v) - g(x)$ on the punctured unit ball
is homotopic in $\R^n \setminus \{0\}$ to $v \mapsto \varepsilon v$;
then $g$ carries the local orientation class at $x$ to the one at
$gx$. On connected $O$ the homotopy class of a local map of $g$
does not depend on the ball. At one fixed ball, continuity of the
action at $0$ gives an open subgroup whose local maps stay within
$\varepsilon/2$ of $v \mapsto \varepsilon v$ on the sphere of radius
$1/2$, onto which the punctured ball retracts; there the
straight-line homotopy avoids $0$, so every element of that subgroup
preserves orientation.

## Sources

- [Preprint source map: `prop:chart-reduction`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Newman rigidity](../background/newman-rigidity.md)
- [Closed subgroups of $\Zp$](../background/padic-subgroups.md)
