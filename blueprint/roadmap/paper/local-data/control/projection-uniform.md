---
article_id: af_5aab3673b167b576deeb76a5
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.π_uniformContinuous
---

# The orbit map is uniformly continuous

For a local datum and $\varepsilon>0$ there is $\delta>0$ such that $d_T(\pi z,\pi w)<\varepsilon$ whenever $z,w\in Z^+$ and $|z-w|<\delta$.

*Proof sketch.* The map $(a,z)\mapsto a\cdot z$ is uniformly continuous on the compact set $\mathbb Z_p\times Z^+$ (Heine–Cantor), so $d_1(z,w)<\varepsilon$ once $|z-w|$ is small, uniformly in $a$. Then use $d_T(\pi z,\pi w)\le d_1(z,w)$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The quotient topology on the control space](control-topology.md)
- [The quotient map to the control space](control-quotient-map.md)
- [The orbit metric on the control space](control-metric.md)

## Proof depends on

- [The test region is compact](../chart/test-region-compact.md)
