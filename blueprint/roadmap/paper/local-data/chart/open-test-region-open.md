---
article_id: af_b1565d28b8471792fa98ddb4
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.isOpen_Uplus
---

# The open test region is open

For a local datum, $U^+$ is open in $\mathbb R^n$ and $U^+\subseteq Z^+$.

*Proof sketch.* $U^+$ is the preimage of an open set under the continuous $F_0$ on the open set $\Omega$; the inclusion is immediate from the definitions.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The test region](test-region.md)
- [The open test region](open-test-region.md)

## Proof depends on

- [The averaged map is continuous](averaged-map-continuous.md)
