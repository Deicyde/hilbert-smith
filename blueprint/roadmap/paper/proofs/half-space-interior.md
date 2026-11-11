---
article_id: af_19cf1c37b3b98a8fa6887dda
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.mem_intrinsicInterior_of_pos
---

# Points over the open half-space are interior

Let $n\ge1$, let $M$ be a topological space, and let $\varphi$ be a homeomorphism from an open set $V\subseteq M$ onto an open subset of the half-space $\{x\in\mathbb{R}^n:x_0\ge0\}$. If $x\in V$ and $\varphi(x)_0>0$, then $x\in M^\circ_n$.

*Proof sketch.* Let $V^+$ be the set of points of $V$ that $\varphi$ maps into the open half-space $\{x_0>0\}$; it is open in $M$. Let $r:\mathbb{R}^n\to\{x_0\ge0\}$ be the continuous retraction replacing $y_0$ by $\max(y_0,0)$. Then $\varphi$, followed by the inclusion of the half-space into $\mathbb{R}^n$, maps $V^+$ homeomorphically onto $\{y:y_0>0\}\cap r^{-1}(\varphi(V))$, which is open in $\mathbb{R}^n$, with inverse $\varphi^{-1}\circ r$. So the open set $V^+\ni x$ is homeomorphic to an open subset of $\mathbb{R}^n$.

## Sources

- Standard; split out of the proofs that the intrinsic interior is dense and connected.

## Depends on

- [Intrinsic interior](intrinsic-interior.md)
