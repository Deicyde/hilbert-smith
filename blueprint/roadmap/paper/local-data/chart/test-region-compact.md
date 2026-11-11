---
article_id: af_a2220fda11e400fdb7b210d6
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.isCompact_Zplus
---

# The test region is compact

For a local datum, $Z^+$ is compact.

*Proof sketch.* By boundedness, $Z^+$ is the set of points of the compact ball $\overline B(0,\rho_++D)\subseteq\Omega$ at which the continuous function $|F_0|$ is at most $\rho_+$: a closed subset of that ball.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The test region](test-region.md)

## Proof depends on

- [The test region is bounded](test-region-bounded.md)
- [The averaged map is continuous](averaged-map-continuous.md)
