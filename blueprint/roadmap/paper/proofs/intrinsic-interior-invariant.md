---
article_id: af_6026f8b12369656ff3114fff
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: HSP.image_intrinsicInterior
---

# The intrinsic interior is invariant

For every topological space $M$, every $n\in\mathbb{N}$ and every homeomorphism $h$ of $M$, $h(M^\circ_n)=M^\circ_n$.

*Proof sketch.* If $U\ni x$ is open with a homeomorphism $\varphi$ onto an open subset of $\mathbb{R}^n$, then $h(U)\ni h(x)$ is open with the homeomorphism $\varphi\circ h^{-1}$. So $h(M^\circ_n)\subseteq M^\circ_n$, and the same for $h^{-1}$ gives equality.

## Sources

- New: the intrinsic definition makes invariance immediate

## Depends on

- [Intrinsic interior](intrinsic-interior.md)
