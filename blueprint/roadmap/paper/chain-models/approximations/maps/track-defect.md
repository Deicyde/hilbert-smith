---
article_id: af_3a38119ca6cb91359db54c3f
declaration: def
origin: bridged
statement: formalized
lean: HSP.ChainModels.trackDefect
---

# Track defect

Fix a [local datum](../../../local-data/chart/local-datum.md), with its domain $\Omega\subseteq\mathbb R^n$ and its $\mathbb Z_p$-action, and let $r_i:\mathbb Z/p^i\to\mathbb Z_p$ be the [representatives of the finite quotients](../../../local-data/control/representative-map.md). The *track defect* at level $i$ is
$$\beta_i=\sup\{|r_i(g)\cdot(r_i(h)\cdot x)-r_i(g+h)\cdot x|:\ g,h\in\mathbb Z/p^i,\ x\in\Omega,\ |x|\le3/8\},$$
the supremum of a set of real numbers (taken to be $0$ if the set is empty or unbounded above).

## Sources

- New: the defect of the representatives as an action, controlled in the properties of completed maps (HS paper, Section 9).

## Depends on

- [Local datum](../../../local-data/chart/local-datum.md)

## Proof depends on

- [Representatives of the finite quotients](../../../local-data/control/representative-map.md)
