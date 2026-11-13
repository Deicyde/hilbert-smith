---
article_id: af_d81ebf590156d5f1d09bae80
declaration: instance
origin: bridged
statement: formalized
lean: HSP.LocalDatum.instAddActionT
---

# The cyclic action on the control space

For a local datum, let $C_p=\mathbb Z/p\mathbb Z$ and let $q_1:\mathbb Z_p\to C_p$ be reduction modulo $p$, whose kernel is $H_1$. Then $C_p$ acts on $T$ by $q_1(a)\cdot\pi(z)=\pi(a\cdot z)$; concretely, $c\in C_p$ acts as its representative in $\{0,\dots,p-1\}$ does, and the formula for every $a$ then holds because the kernel of $q_1$ is $H_1$. This is well defined because $\mathbb Z_p$ is abelian: if $q_1(a)=q_1(a')$ and $\pi z=\pi z'$, then $a\cdot z$ and $a'\cdot z'$ differ by an element of $H_1$.

## Sources

- [OpenAI preprint, Section 5](../../../../sources/preprint.md#section-5-local-tests-sections05-local-teststex), 05-local-tests.tex lines 117-131
- [HS paper, Section 8](../../../../sources/hs-paper.md#section-8-geometric-data-and-quotient-representatives-geofixed-data-lines-755-846)

## Depends on

- [The control space](control-space.md)
- [Local datum](../chart/local-datum.md)

## Proof depends on

- [The test region](../chart/test-region.md)
- [The quotient map to the control space](control-quotient-map.md)
- [The action on the test region](zplus-action.md)
- [The subgroups $H_j$](../subgroups/padic-subgroups.md)
