---
article_id: af_04d37a385ae04e8c7208ce4d
declaration: lemma
origin: bridged
---

# The control space is a compact metric space

For a local datum, $d_T$ is a metric on $T$ that induces the quotient topology, and $T$ is compact.

*Proof sketch.* Symmetry and the triangle inequality follow from invariance of $d_1$; if $d_T(\pi z,\pi w)=0$ then the minimum gives $z=b\cdot w$ for some $b\in H_1$, so $\pi z=\pi w$. $T$ is compact as a continuous image of the compact $Z^+$. Since $d_T(\pi z,\pi w)\le d_1(z,w)$, the map $\pi$ is continuous into $(T,d_T)$, so the identity from the compact quotient space to the Hausdorff metric space is a continuous bijection, hence a homeomorphism.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The orbit metric on the control space](control-metric.md)

## Proof depends on

- [The orbit sup-distance is an invariant metric](orbit-sup-metric-properties.md)
- [The test region is compact](../chart/test-region-compact.md)
