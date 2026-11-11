---
article_id: af_9bb9647151149f0e9b889af8
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.dT_vadd
---

# The cyclic action is isometric

For a local datum, $d_T(c\cdot s,c\cdot t)=d_T(s,t)$ for all $c\in C_p$ and $s,t\in T$. Hence $C_p$ acts by isometries of the metric space $(T,d_T)$.

*Proof sketch.* Write $c=q_1(a)$ with $a\in\{0,\dots,p-1\}$ the representative of $c$, and $s=\pi z$, $t=\pi w$. Then $d_T(\pi(a\cdot z),\pi(a\cdot w))=\inf_b d_1(a\cdot z,b\cdot(a\cdot w))=\inf_b d_1(a\cdot z,a\cdot(b\cdot w))=\inf_b d_1(z,b\cdot w)$, using that $\mathbb Z_p$ is abelian and the invariance of $d_1$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The action on the test region](zplus-action.md)
- [The cyclic action on the control space](control-action.md)
- [The orbit metric on the control space](control-metric.md)
- [The orbit metric metrizes the control space](control-metric-properties.md)

## Proof depends on

- [The orbit sup-distance is invariant](orbit-sup-metric-invariant.md)
