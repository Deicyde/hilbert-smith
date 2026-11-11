---
article_id: af_45ac8e58f08b7383137b2360
declaration: instance
origin: background
statement: formalized
lean: HSP.DualityPairing.additive_curry_obj
---

# A duality pairing is additive in the second variable

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md). For every object $N$ of $\mathcal B$ the functor $N\boxtimes-:\mathcal E\to\mathcal B''$ is additive: $1_N\boxtimes(g+g')=1_N\boxtimes g+1_N\boxtimes g'$.

*Proof sketch.* This is the additivity of $\boxtimes$ in the second variable, one of the axioms of a duality pairing, applied with $f=1_N$.

## Sources

- New: a restatement of an axiom of duality pairings.

## Depends on

- [Duality pairings](../duality-pairing.md)
