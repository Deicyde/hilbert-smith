---
article_id: af_61b1e04079d960213bc6a15b
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.exists_moved_of_mem_Zplus
---

# No point of the test region is fixed

For a local datum, every $z\in Z^+$ is moved by some $a\in\mathbb Z_p$.

*Proof sketch.* A point $x$ fixed by all of $\mathbb Z_p$ satisfies $F_0(x)=x$, so $|x|\le\rho_+$, which the condition of no fixed points near the origin excludes.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The test region](test-region.md)

## Proof depends on

- [The averaged map at a fixed point](averaged-map-fixed.md)
