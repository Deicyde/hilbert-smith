---
article_id: af_0a60c47824a088017bd7b348
declaration: lemma
origin: cited
lean: HilbertSmith.exists_open_disjoint_smul HilbertSmith.sheet_open HilbertSmith.sheet_pairwise_disjoint HilbertSmith.sheet_union HilbertSmith.sheetImage_open HilbertSmith.sheetImage_nonempty HilbertSmith.sheet_homeomorph HilbertSmith.sheet_unique HilbertSmith.sheet_exists HilbertSmith.sheetCoord HilbertSmith.sheetCoord_mem HilbertSmith.sheetCoord_unique HilbertSmith.shift_mem HilbertSmith.sheetCoord_shift HilbertSmith.sheetCoord_locallyConstant HilbertSmith.sheetBeta HilbertSmith.sheetBeta_locallyConstant HilbertSmith.sheetBeta_equivariant HilbertSmith.exp_pow_nat HilbertSmith.zeta_pow_eq_one HilbertSmith.cyclicChar HilbertSmith.cyclic_card HilbertSmith.sheetBeta_cyclic_equivariant HilbertSmith.sheetBeta_cyclic_mem
statement: formalized
proof: formalized
---

# Finite quotient sheets

For every $k \geq 1$, with $m = p^k$ and
$\zeta = \exp(2\pi i/m)$, there is a nonempty open
$V \subset Y \setminus \{y_\infty\}$ over which the finite quotient
$W/(p^kG) \to W/G$ is a disjoint union of $m$ homeomorphisms onto
$V$. There is a locally constant
$\beta : q^{-1}(V) \to \{1, \zeta, \ldots, \zeta^{m-1}\}$ with
$\beta(gw) = \zeta^{\bar g}\beta(w)$ for
$\bar g \in G/p^kG = \Z/m$.

*Proof sketch.* Some $x \in W$ has stabilizer inside $p^kG$,
or $p^{k-1}G$ would fix everything, contradicting faithfulness.
On $Z = W/p^kG$ the finite cyclic action is free at the image of
$x$; disjoint neighborhoods of its orbit intersected over
translates give $N$ with disjoint translates, and the open finite
quotient map restricts to homeomorphisms on each. Constant values
$\zeta^j$ on the pulled-back sheets give $\beta$.

## Sources

- [Preprint source map: `lem:finite-sheets`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Closed subgroups of $\Zp$](../background/padic-subgroups.md)
