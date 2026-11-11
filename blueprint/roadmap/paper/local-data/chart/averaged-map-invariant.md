---
article_id: af_dd9c112b59eeec724fad55b5
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.F₀_vadd
---

# The averaged map is invariant

For a local datum, $F_0(b\cdot x)=F_0(x)$ for all $b\in\mathbb Z_p$ and $x\in\Omega$.

*Proof sketch.* Write $a\cdot(b\cdot x)=(a+b)\cdot x$ and use translation invariance of $\mu$.

## Sources

- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)
- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 163-175 (an analogous average, of a pinch map)

## Depends on

- [The averaged chart map](averaged-map.md)

## Proof depends on

- [The Haar probability measure on $\mathbb Z_p$](../subgroups/haar-zp.md)
