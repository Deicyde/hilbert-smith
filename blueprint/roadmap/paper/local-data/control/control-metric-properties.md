---
article_id: af_04d37a385ae04e8c7208ce4d
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.dT_metric
---

# The orbit metric metrizes the control space

For a local datum, $d_T$ is a metric on $T$ that induces the quotient topology.

*Proof sketch.* Symmetry and the triangle inequality follow from those of $d_1$ and its invariance, reindexing over $H_1$. If $d_T(\pi z,\pi w)=0$, the infimum over the compact $H_1$ of the continuous function $b\mapsto d_1(z,b\cdot w)$ is attained, so $z=b\cdot w$ for some $b\in H_1$ and $\pi z=\pi w$. A set $U\subseteq T$ is open in the quotient topology if and only if $\pi^{-1}(U)$ is open in $Z^+$, whose topology $d_1$ induces. Since $d_T(\pi z,\pi w)\le d_1(z,w)$, a $d_T$-open $U$ has open preimage. Conversely, if $\pi^{-1}(U)$ is open and contains $z$, it contains every $w'$ with $d_1(z,w')<\varepsilon$ for some $\varepsilon>0$; if $d_T(\pi z,\pi w)<\varepsilon$ then $d_1(z,b\cdot w)<\varepsilon$ for some $b\in H_1$, so $\pi w=\pi(b\cdot w)\in U$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The orbit metric on the control space](control-metric.md)

## Proof depends on

- [The orbit sup-distance is a metric](orbit-sup-metric-properties.md)
- [The orbit sup-distance is invariant](orbit-sup-metric-invariant.md)
- [The subgroups $H_j$ form a basis at $0$](../subgroups/padic-subgroups-basis.md)
