---
article_id: af_9f9005872fa408e9069f3b2e
declaration: lemma
origin: background
statement: formalized
lean: HSP.ultL.of_eq_zero_iff
proof: formalized
---

# Classes zero in the colimit

For $x\in L^{\langle -j\rangle}_k(\mathcal A)$, $\iota_j x=0$ if and only if $t^m x=0$ in $L^{\langle -j-m\rangle}_k(\mathcal A)$ for some $m\ge0$.

*Proof sketch.* If $t^mx=0$ then $\iota_jx=\iota_{j+m}t^mx=0$ by [Stages are compatible with the transition](level-compatible.md). Conversely, an element of one stage that becomes zero in the colimit of a sequence of groups is already zero at some later stage.

## Sources

- New: property of the colimit.

## Depends on

- [Ultimate L-group](ultimate-l-group.md)

## Proof depends on

- [Stages are compatible with the transition](level-compatible.md)
