---
article_id: af_08201599c9e8dd09f5eeb0bb
declaration: theorem
origin: background
statement: formalized
lean: HSP.newman_small_orbits
---

# Newman's theorem: small orbits

Let $M$ be a topological space and $e$ an open partial homeomorphism from $M$ to $\mathbb R^n$, that is, a homeomorphism from an open subset of $M$ (its domain) onto an open subset of $\mathbb R^n$ (its target), whose target contains the closed unit ball $\bar B$. For $S\subseteq\bar B$ write $e^{-1}(S)$ for the set of points of the domain that $e$ maps into $S$, which is the image of $S$ under the inverse of $e$. Then there is $\delta>0$ with the following property. Let $q$ be any prime and $g$ any homeomorphism of $M$ with $g^q=\mathrm{id}$. Suppose that for every $k\ge0$ and every $x\in e^{-1}(\bar B)$, the point $g^kx$ lies in the domain of $e$ and $|e(g^kx)-e(x)|<\delta$. Then $g$ fixes every point of $e^{-1}(B)$, where $B$ is the open unit ball.

**Remark (not formalized).** This is an open statement: the Lean states it now and proves it later. Planned route. Newman's orbit-diameter argument [U], or Dress's treatment [U], run with $\mathbb Z/q$ coefficients on the closed chart ball $e^{-1}(\bar B)$ only. The uniformity of $\delta$ in the prime $q$ is the part that has not been checked against a published statement (see the chapter introduction).

**Remark (not formalized).** Here $\delta$ depends on $M$ and $e$ but on neither $q$ nor $g$. The displacement condition is on the whole cyclic orbit, not on $g$ alone. Together with Newman's theorem on fixing an open set it gives the global form: on a connected manifold, such a $g$ is the identity.

## Sources

- Published: M. H. A. Newman, A theorem on periodic transformations of spaces, Quart. J. Math. 2 (1931), the orbit-diameter form (not checked against the original)
- Published: P. A. Smith, Transformations of finite period III, Ann. of Math. 42 (1941) (not checked against the original)
- Published: A. Dress (1969), Newman's theorems for compact Lie groups (title and journal not checked)

## Depends on
