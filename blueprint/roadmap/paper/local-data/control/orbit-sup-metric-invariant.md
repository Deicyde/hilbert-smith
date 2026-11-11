---
article_id: af_5412e775425ab1c9a9725a76
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: HSP.LocalDatum.d₁_vadd
---

# The orbit sup-distance is invariant

For a local datum, $d_1(b\cdot z,b\cdot w)=d_1(z,w)$ for all $b\in\mathbb Z_p$ and $z,w\in Z^+$.

*Proof sketch.* Both sides are maxima over $a\in\mathbb Z_p$, and $a\cdot(b\cdot z)=(a+b)\cdot z$; reindexing by $a\mapsto a+b$, a bijection of $\mathbb Z_p$, turns one maximum into the other.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131

## Depends on

- [The orbit sup-distance on the test region](orbit-sup-metric.md)
- [The action on the test region](zplus-action.md)
