---
article_id: af_03e1a41a9dea9c1ac2875cfe
declaration: def
origin: bridged
statement: formalized
lean: HSP.LocalDatum.T
---

# The control space

For a local datum, the control space is $T=Z^+/H_1$, the set of $H_1$-orbits of the restricted action on $Z^+$, with [quotient map](control-quotient-map.md) $\pi:Z^+\to T$ and the [quotient topology](control-topology.md).

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131
- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846) (there a detector map to a separately chosen space plays this role)
- New: the control space is the orbit space itself, so no detector is needed

## Depends on

- [Local datum](../chart/local-datum.md)

## Proof depends on

- [The test region](../chart/test-region.md)
- [The action on the test region](zplus-action.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)
