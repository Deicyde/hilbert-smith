---
article_id: af_e29fa47cce87cfd0f009bce6
declaration: lemma
origin: bridged
---

# The cyclic action is free

For a local datum, if $c\in C_p$, $t\in T$ and $c\cdot t=t$, then $c=0$.

*Proof sketch.* Write $t=\pi z$ and $c=q_1(a)$. Then $\pi(a\cdot z)=\pi z$, so $a\cdot z=b\cdot z$ for some $b\in H_1$. The element $a-b$ fixes $z$, so it lies in $H_1$ by the lemma on stabilizers on the test region. Hence $a\in H_1$ and $c=0$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (freeness of the cyclic action on the control space)

## Depends on

- [The cyclic action on the control space](control-action.md)

## Proof depends on

- [Stabilizers on the test region](../chart/stabilizers-on-test-region.md)
- [The kernel of reduction modulo $p^i$](reduction-kernel.md)
