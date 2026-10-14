---
article_id: af_0a60c47824a088017bd7b348
declaration: lemma
origin: cited
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
