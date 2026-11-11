---
article_id: af_da10ec4d777701af54d1f3aa
declaration: lemma
origin: bridged
statement: formalized
lean: HSP.LocalDatum.compactSpace_T
---

# The control space is compact

For a local datum, the control space $T$ is compact in the quotient topology.

*Proof sketch.* The quotient map $\pi:Z^+\to T$ is continuous and surjective, and $Z^+$ is compact, so $T=\pi(Z^+)$ is compact.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The control space](control-space.md)

## Proof depends on

- [The test region is compact](../chart/test-region-compact.md)
