---
article_id: af_b4680d3de8e7053cef4390f7
declaration: lemma
origin: cited
---

# Odd-sphere nullhomotopy

Let $d \geq 3$ be odd. If $K$ is compact metrizable and
$v : K \to S^d$ satisfies $v^*\gamma_d = 0$, then there are a
positive integer $s$ and a degree-$s$ map $D_s : S^d \to S^d$ with
$D_s v$ nullhomotopic.

*Proof sketch.* Approximate $v$ by a map factoring through a finite
nerve, then refine so the finite-complex map is rationally trivial.
The mapping telescope of degree $2, 3, \ldots$ maps has type
$K(\Q, d)$: Serre finiteness plus the degree-map killing assertion
kill all higher homotopy, and the degree-$d$ direct limit is $\Q$.
Eilenberg--MacLane representability nullhomotopes the composite
into the telescope; bounded height retracts to a finite stage,
giving the nullhomotopy of $D_s v$ for a product of the displayed
degrees.

## Sources

- [Preprint source map: `lem:odd-sphere-null`](../../sources/preprint.md)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Serre odd-sphere maps](../background/serre-maps.md)
- [Cech comparison](../background/cech-comparison.md)
