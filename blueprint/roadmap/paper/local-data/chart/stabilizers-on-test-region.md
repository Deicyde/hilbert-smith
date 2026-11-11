---
article_id: af_aeb70523ebe6b43dee1218ca
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.stabilizer_le
---

# Stabilizers on the test region

For a local datum and $z\in Z^+$, the stabilizer $\{a\in\mathbb Z_p:a\cdot z=z\}$ is contained in $H_1$.

*Proof sketch.* The stabilizer is a closed subgroup, since $\Omega$ is Hausdorff and the action is continuous, and it is not $\mathbb Z_p$ because no point of the test region is fixed. So it lies in $H_1$ by the lemma on proper closed subgroups.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The test region](test-region.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)

## Proof depends on

- [No point of the test region is fixed](test-region-not-fixed.md)
- [Proper closed subgroups lie in $p\mathbb Z_p$](../subgroups/proper-closed-subgroups.md)
