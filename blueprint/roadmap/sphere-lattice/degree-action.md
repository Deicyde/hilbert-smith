---
article_id: af_b69d958f6ab4f0bf67199844
declaration: theorem
origin: cited
---

# Action of degree

Let $d \geq 3$ be odd. If $f : S^d \to S^d$ is continuous of degree
$s \in \Z$, then $f_*\bar u_d = s\bar u_d$ in
$E_d(S^d) \otimes \Q$; hence $f_*$ acts on the whole rational group
by $s$. More generally, if $N$ is a connected closed oriented
triangulable $d$-manifold and $f : N \to S^d$ has degree $s$, its
pushed orientation form has rational class $s\bar u_d$.

*Proof sketch.* Simplicially approximate $f$ after subdivision on
semialgebraic models; homotopy invariance identifies $f_*$ and
$g_*$ on the continuous theory. Over a ball in a top-dimensional
target simplex, the map is finitely many homeomorphic sheets; the
pushed pairing is diagonal with $\pm 1$ entries by orientation
signs, and its signature is the degree by the local-degree formula.
Clearing denominators against a signature ball inside the sheet
ball determines the rational coefficient; the comparison transfers
it to $E$, where $\bar u_d$ spans.

## Sources

- [Preprint source map: `prop:degree-action`](../../sources/preprint.md)

## Depends on

- [Test categories](../sheaf-categories/test-categories.md)
- [Fixed sphere lattice](sphere-lattice.md)

## Proof depends on

- [Fixed sphere lattice](sphere-lattice.md)
- [Homotopy invariance](../sheaf-categories/homotopy-invariance.md)
- [Hatcher degree facts](../background/hatcher-facts.md)
- [Direct images and open extension](../sheaf-categories/test-pushforward.md)
