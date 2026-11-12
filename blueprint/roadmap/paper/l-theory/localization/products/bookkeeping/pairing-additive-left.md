---
article_id: af_2163ccddd19d7916c614950a
declaration: instance
origin: background
statement: formalized
lean: HSP.DualityPairing.additive_curry
---

# A duality pairing is additive in the first variable

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md). Then $N\mapsto N\boxtimes-$ is an additive functor from $\mathcal B$ to the category of functors $\mathcal E\to\mathcal B''$: $(f+f')\boxtimes1_V=f\boxtimes1_V+f'\boxtimes1_V$ for all $f,f':N\to N'$ and objects $V$ of $\mathcal E$.

*Proof sketch.* This is the additivity of $\boxtimes$ in the first variable, one of the axioms of a duality pairing, applied with $g=1_V$.

## Sources

- New: a restatement of an axiom of duality pairings.

## Depends on

- [Duality pairings](../duality-pairing.md)
