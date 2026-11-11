---
article_id: af_5ba8d1a7ad3e2fe7af2ccbe0
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.d₁_metric
---

# The orbit sup-distance is a metric

For a local datum, $d_1$ is a metric on $Z^+$ that induces the subspace topology of $Z^+\subseteq\mathbb R^n$.

*Proof sketch.* The metric axioms hold pointwise in $a$ and pass to the supremum, which is finite because $\mathbb Z_p$ is compact and the action is continuous. Since $|z-w|\le d_1(z,w)$, the $d_1$-topology is at least as fine as the Euclidean one. Conversely, by the tube lemma for the compact group $\mathbb Z_p$ and the joint continuity of $(a,w)\mapsto|a\cdot z-a\cdot w|$, every $d_1$-ball about $z$ contains a Euclidean neighbourhood of $z$, so the topologies agree.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The orbit sup-distance on the test region](orbit-sup-metric.md)
