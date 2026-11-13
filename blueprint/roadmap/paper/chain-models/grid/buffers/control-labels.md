---
article_id: af_eeca84e6f0698ef8f0ed946d
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.controlLabel
---
# Control labels

Fix a local datum and $0<\rho<\rho_+$, with $f_T$ and the sphere labels of radius $\rho$, and a real number $v$ (in use $v>0$). The *control label* of a [buffered cell](buffered-cells.md) $b\in\mathcal B_i(v)$, a cell of $D_i$ or its dual, is
$$\lambda(b)=(\pi(\tilde x_b),s_b)\in T\times S^n,$$
where $\tilde x_b\in[-2,2)^n$ is the lift of its torus label $x_b$, $s_b$ is its [sphere label](../sphere-labels.md), and $\pi:Z^+\to T$ is the quotient map onto the [control space](../../../local-data/control/control-space.md). Cells that are not buffered get no control label. $T\times S^n$ carries the maximum of $d_T$ and $d_S$ and the action of $C_p$ on $T$, as for [graph-type matrices](../../../corner/actions/graph-type.md).

More generally, for any set of cells $B$ (finiteness is not needed) with torus labels $x_b$ and $b\in\mathcal B(v)$ (the [buffered cells](buffered-cells.md) of $B$), $\lambda(b)=(\pi(\tilde x_b),f_T(x_b))$; for the cells of $D_i$ and $D_i^{N-*}$ this is the label above, since $f_T(x_b)=s_b$.

This is well defined: $\tilde x_b$ lies in the [test region](../../../local-data/chart/test-region.md) $Z^+$. Indeed $f(\tilde x_b)=f_T(x_b)=s_b$ by the definition of the [torus test map](../../approximations/torus-test-map.md), and $s_b$ lies in the compact set $\overline B(0,v)\subseteq\mathbb R^n$, so $\tilde x_b\in U^+$ by [preimages under the test map](../../../local-data/chart/test-map-proper.md); and the [open test region](../../../local-data/chart/open-test-region.md) $U^+=\{|F_0|<\rho_+\}$ lies in $Z^+=\{|F_0|\le\rho_+\}$.

## Sources
- HS paper, Sections 9-10 (labels on the buffered domain).
## Depends on

- [Buffered cells](buffered-cells.md)
- [The control space](../../../local-data/control/control-space.md)
- [The torus](../torus.md)
- [The round sphere](../../../corner/round-sphere.md)
- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [Buffered sphere labels](buffered-sphere-labels.md)
- [Torus test map](../../approximations/torus-test-map.md)
- [The lift](../../torus/lift.md)
- [The averaged chart map](../../../local-data/chart/averaged-map.md)
- [The open test region](../../../local-data/chart/open-test-region.md)
- [Preimages under the test map](../../../local-data/chart/test-map-proper.md)
- [The test map](../../../local-data/chart/test-map.md)
- [The test region](../../../local-data/chart/test-region.md)
- [The quotient map to the control space](../../../local-data/control/control-quotient-map.md)
