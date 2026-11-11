---
article_id: af_6573703e235dff65f87aba40
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.ι_π_self
proof: formalized
---

# Projection after inclusion of the same summand

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. If $p+q=r$, then $\pi_{p,q}\iota_{p,q}=1$ on $C_p\boxtimes E_q$, for the [summand inclusion](summand-inclusion.md) and [summand projection](summand-projection.md) of degree $r$.

*Proof sketch.* By definition $\pi_{p,q}$ restricts to the identity on the summand $C_p\boxtimes E_q$.

## Sources

- New: direct from the definitions.

## Depends on

- [Summand inclusions of a tensor product](summand-inclusion.md)
- [Summand projections of a tensor product](summand-projection.md)
