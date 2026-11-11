---
article_id: af_46ebd8e9c32e3f3d01810c7a
declaration: lemma
origin: background
statement: formalized
lean: HSP.cxProd.isZero_of_not_mem_supp
proof: formalized
---

# Summands outside the support vanish

Let $(\boxtimes,\kappa):\mathcal B\times\mathcal E\to\mathcal B''$ be a [duality pairing](../duality-pairing.md), and $C$ a complex in $\mathcal B$ and $E$ a complex in $\mathcal E$, each with all but finitely many chain objects zero objects. If $p+q=r$ and $(p,q)$ is not in the [support](product-support.md) of degree $r$, then $C_p\boxtimes E_q$ is a zero object.

*Proof sketch.* One of $C_p$, $E_q$ is a zero object, say $C_p$, so $1_{C_p}=0$. Then $1_{C_p\boxtimes E_q}=1_{C_p}\boxtimes1_{E_q}=0\boxtimes1_{E_q}=0$, since $\boxtimes$ is additive in each variable; likewise if $E_q$ is a zero object.

## Sources

- New: direct from the axioms of duality pairings.

## Depends on

- [Duality pairings](../duality-pairing.md)
- [Support of a tensor product of complexes](product-support.md)
