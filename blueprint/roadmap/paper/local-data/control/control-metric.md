---
article_id: af_e5176fb9dbfe8fa21906f55d
declaration: def
origin: bridged
statement: formalized
lean: HSP.LocalDatum.dT
---

# The orbit metric on the control space

For a local datum, define $d_T(\pi z,\pi w)=\inf_{b\in H_1}d_1(z,b\cdot w)$ for $z,w\in Z^+$. The value does not depend on the representatives $z,w$, because $d_1$ is $\mathbb Z_p$-invariant and $\mathbb Z_p$ is abelian.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The action on the test region](zplus-action.md)
- [The control space](control-space.md)
- [The orbit sup-distance on the test region](orbit-sup-metric.md)

## Proof depends on

- [The orbit sup-distance is invariant](orbit-sup-metric-invariant.md)
