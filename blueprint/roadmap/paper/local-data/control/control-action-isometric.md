---
article_id: af_9bb9647151149f0e9b889af8
declaration: lemma
origin: bridged
---

# The cyclic action is isometric

For a local datum, $d_T(c\cdot s,c\cdot t)=d_T(s,t)$ for all $c\in C_p$ and $s,t\in T$.

*Proof sketch.* Write $c=q_1(a)$, $s=\pi z$, $t=\pi w$. Then $d_T(\pi(a\cdot z),\pi(a\cdot w))=\min_b d_1(a\cdot z,b\cdot(a\cdot w))=\min_b d_1(a\cdot z,a\cdot(b\cdot w))=\min_b d_1(z,b\cdot w)$ by invariance of $d_1$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The cyclic action on the control space](control-action.md)
- [The orbit metric on the control space](control-metric.md)

## Proof depends on

- [The orbit sup-distance is invariant](orbit-sup-metric-invariant.md)
