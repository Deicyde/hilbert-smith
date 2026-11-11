---
article_id: af_43deb88f4cfdae10ed0b7013
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.ι_π_of_ne
proof: formalized
---

# Projection after inclusion of another summand

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. If $(p,q)\ne(p',q')$, then $\pi_{p',q'}\iota_{p,q}=0$ from $C_p\boxtimes E_q$ to $C_{p'}\boxtimes E_{q'}$, for the [summand inclusion](summand-inclusion.md) and [summand projection](summand-projection.md) of any degree $r$.

*Proof sketch.* If $p+q\ne r$ then $\iota_{p,q}=0$. Otherwise $\pi_{p',q'}$ restricts to $0$ on the summand $C_p\boxtimes E_q$ by definition.

## Sources

- New: direct from the definitions.

## Depends on

- [Summand inclusions of a tensor product](summand-inclusion.md)
- [Summand projections of a tensor product](summand-projection.md)
